/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen, Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Resultant of two polynomials

This file contains basic facts about resultant of two polynomials over commutative rings.

## Main definitions

* `Polynomial.resultant`: The resultant of two polynomials `p` and `q` is defined as the determinant
  of the Sylvester matrix of `p` and `q`.
* `Polynomial.discr`: The discriminant of a polynomial `f` is defined as the resultant of `f` and
  `f.derivative`, modified by factoring out a sign and a power of the leading term.

## TODO

* The eventual goal is to prove the following property:
  `resultant (∏ a ∈ s, (X - C a)) f = ∏ a ∈ s, f.eval a`.
  This allows us to write the `resultant f g` as the product of terms of the form `a - b` where `a`
  is a root of `f` and `b` is a root of `g`.
* Resultant of two binary forms (i.e. homogeneous polynomials in two variables), after binary forms
  are implemented.
-/

@[expose] public section

open Set

namespace Polynomial

section sylvester

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respectively is a
`(m+n) × (m+n)` matrix with the coefficients of `f` and `g` arranged in a specific way. Here, `m`
and `n` are free variables, not necessarily equal to the actual degrees of the polynomials `f` and
`g`.

Note that the natural definition would be a `Matrix (Fin (m + n)) (Fin m ⊕ Fin n) R` but we prefer
having this as a square matrix to take determinants later on.
-/
/-
**Polynomial.sylvester** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：sylvester (f g : R[X]) (m n : Nat) : Matrix (Fin (m + n)) (Fin (m + n)) R
参数：f g : R[X]；m n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respe
ctively is a
`(m+n) × (m+n)` matrix with the coefficients of `f` and `g` arranged in a specif
ic way. Here, `m`
and `n` are free variables, not necessarily equal to the actual degrees of the p
olynomials `f` and
`g`.

Note that the natural definition would be a `Matrix (Fin (m + n)) (Fin m ⊕ Fin n
) R` but we prefer
having this as a square matrix to take determinants later on.
-/
def sylvester (f g : R[X]) (m n : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
  .of fun i j ↦ j.addCases
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then g.coeff (i - j₁) else 0)
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then f.coeff (i - j₁) else 0)

variable (f g : R[X]) (m n : ℕ)
/-
**Polynomial.sylvester_zero_left_deg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (f g : Polynomial R) (m : ℕ),   f.syl
vester g 0 m = Matrix.diagonal fun x => f.coeff 0
参数：f g : Polynomial R；m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sylvester.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f g : P
olynomial R) (m n : ℕ),   f.sylvester g m n =     Matrix.of fun i j =>       Fin
.addCases (fun …
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
· 使用定理 `Matrix.diagonal_apply`：diagonal_apply [Zero α] (d : n -> α) (i j) : diag
onal d i j = if i = j then d i else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.natAdd_zero`：∀ {n : ℕ}, Fin.natAdd 0 = Fin.cast ⋯
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
@[simp] theorem sylvester_zero_left_deg :
    sylvester f g 0 m = Matrix.diagonal (fun _ ↦ f.coeff 0) :=
  Matrix.ext fun i j ↦ j.addCases nofun fun j ↦ by
    rw [sylvester, Matrix.of_apply, Fin.addCases_right, Matrix.diagonal_apply]
    split_ifs <;> simp_all [Fin.ext_iff]
/-
**Polynomial.sylvester_comm** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：sylvester_comm : sylvester f g m n = (sylvester g f n m).reindex (finCongr
 (add_comm n m)) (finSumFinEquiv.symm.trans <| (Equiv.sumComm _ _).trans finSumF
inEquiv)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
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
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `finSumFinEquiv_symm_apply_castAdd`：finSumFinEquiv_symm_apply_castAdd (x 
: Fin m) : finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finSumFinEquiv_symm_apply_natAdd`：finSumFinEquiv_symm_apply_natAdd (x : 
Fin n) : finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x
-/
lemma sylvester_comm :
    sylvester f g m n = (sylvester g f n m).reindex (finCongr (add_comm n m))
      (finSumFinEquiv.symm.trans <| (Equiv.sumComm _ _).trans finSumFinEquiv) := by
  ext i j
  induction j using Fin.addCases <;> simp [sylvester]
/-
**Polynomial.sylvester_map_map** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：sylvester_map_map (φ : R ->+* S) : sylvester (f.map φ) (g.map φ) m n = φ.m
apMatrix (sylvester f g m n)
参数：φ : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
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
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
-/
lemma sylvester_map_map (φ : R →+* S) :
    sylvester (f.map φ) (g.map φ) m n = φ.mapMatrix (sylvester f g m n) := by
  ext i j; induction j using Fin.addCases <;> simp [sylvester, apply_ite φ]

/--
The Sylvester matrix for `f` and `f.derivative`, modified by dividing the bottom row by
the leading coefficient of `f`. Important because its determinant is (up to a sign) the
discriminant of `f`.
-/
/-
**Polynomial.sylvesterDeriv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：sylvesterDeriv (f : R[X]) : Matrix (Fin (f.natDegree - 1 + f.natDegree)) (
Fin (f.natDegree - 1 + f.natDegree)) R
参数：f : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Sylvester matrix for `f` and `f.derivative`, modified by dividing the bottom
 row by
the leading coefficient of `f`. Important because its determinant is (up to a si
gn) the
discriminant of `f`.
-/
noncomputable def sylvesterDeriv (f : R[X]) :
    Matrix (Fin (f.natDegree - 1 + f.natDegree)) (Fin (f.natDegree - 1 + f.natDegree)) R :=
  letI n := f.natDegree
  if hn : n = 0 then 0
  else (f.derivative.sylvester f (n - 1) n).updateRow ⟨2 * n - 2, by lia⟩
    (fun j ↦ if ↑j = n - 2 then 1 else (if ↑j = 2 * n - 2 then n else 0))

/-- We can get the usual Sylvester matrix of `f` and `f.derivative` back from the modified one
by multiplying the last row by the leading coefficient of `f`. -/
/-
**Polynomial.sylvesterDeriv_updateRow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：sylvesterDeriv_updateRow (f : R[X]) (hf : 0 < f.natDegree) : (sylvesterDer
iv f).updateRow ⟨2 * f.natDegree - 2, by lia⟩ (f.leadingCoeff • (sylvesterDeriv 
f ⟨2 * f.natDegree - 2, by lia⟩)) = (f.derivative.sylvester f (f.natDegree - 1) 
f.natDegree)
参数：f : R[X]；hf : 0 < f.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sylvesterDeriv.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f 
: Polynomial R),   f.sylvesterDeriv =     if hn : f.natDegree = 0 then 0     els
e       ((Polynomial…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `Fin.ne_of_val_ne`：∀ {n : ℕ} {i j : Fin n}, ↑i ≠ ↑j → i ≠ j
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.coeff_derivative`：coeff_derivative (p : R[X]) (n : Nat) : coe
ff (derivative p) n = coeff p (n + 1) * (n + 1)
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
We can get the usual Sylvester matrix of `f` and `f.derivative` back from the mo
dified one
by multiplying the last row by the leading coefficient of `f`.
-/
lemma sylvesterDeriv_updateRow (f : R[X]) (hf : 0 < f.natDegree) :
    (sylvesterDeriv f).updateRow ⟨2 * f.natDegree - 2, by lia⟩
      (f.leadingCoeff • (sylvesterDeriv f ⟨2 * f.natDegree - 2, by lia⟩)) =
    (f.derivative.sylvester f (f.natDegree - 1) f.natDegree) := by
  by_cases hn : f.natDegree = 0
  · ext ⟨i, hi⟩; lia
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [sylvesterDeriv, dif_neg hn]
  rcases ne_or_eq i (2 * f.natDegree - 2) with hi' | rfl
  · -- Top part of matrix
    rw [Matrix.updateRow_ne (Fin.ne_of_val_ne hi'),
      Matrix.updateRow_ne (Fin.ne_of_val_ne hi')]
  · -- Bottom row
    simp only [sylvester, Fin.addCases, mem_Icc, coeff_derivative, eq_rec_constant, leadingCoeff,
      Matrix.updateRow_self, Matrix.updateRow_apply, ↓reduceIte, Pi.smul_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Matrix.of_apply, Fin.castLT_mk, tsub_le_iff_right, Fin.cast_mk,
      Fin.subNat_mk, dite_eq_ite]
    split_ifs
    on_goal 2 => rw [show f.natDegree = 1 by lia]
    on_goal 3 =>
      rw [← Nat.cast_one (R := R), ← Nat.cast_add, show f.natDegree = 1 by lia]
      norm_num
    on_goal 6 =>
      rw [← Nat.cast_one (R := R), ← Nat.cast_add]
      #adaptation_note
      /--
      Prior to nightly-2025-09-09,
      these two steps were not needed (i.e. `grind` just finished from here)
      -/
      have : 2 * f.natDegree - 2 - (j - (f.natDegree - 1)) + 1 = f.natDegree := by grind
      simp [this]
    all_goals grind

end sylvester

section resultant

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The resultant of two polynomials `f` and `g` is the determinant of the Sylvester matrix of `f`
and `g`. The size arguments `m` and `n` are implemented as `optParam`, meaning that the default
values are `f.natDegree` and `g.natDegree` respectively, but they can also be specified to be
other values. -/
/-
**Polynomial.resultant** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：resultant (f g : R[X]) (m : Nat
参数：f g : R[X]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The resultant of two polynomials `f` and `g` is the determinant of the Sylvester
 matrix of `f`
and `g`. The size arguments `m` and `n` are implemented as `optParam`, meaning t
hat the default
values are `f.natDegree` and `g.natDegree` respectively, but they can also be sp
ecified to be
other values.
-/
def resultant (f g : R[X]) (m : ℕ := f.natDegree) (n : ℕ := g.natDegree) : R :=
  (sylvester f g m n).det

variable (f g p : R[X]) (r : R) (m n k : ℕ)

@[simp]
/-
**Polynomial.resultant_map_map** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_map_map (φ : R ->+* S) : resultant (f.map φ) (g.map φ) m n = φ (
resultant f g m n)
参数：φ : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用引理 `Polynomial.sylvester_map_map`：sylvester_map_map (φ : R ->+* S) : sylvest
er (f.map φ) (g.map φ) m n = φ.mapMatrix (sylvester f g m n)
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resultant_map_map (φ : R →+* S) :
    resultant (f.map φ) (g.map φ) m n = φ (resultant f g m n) := by
  simp [resultant, Polynomial.sylvester_map_map, RingHom.map_det]
/-
**Polynomial.resultant_zero_left_deg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (f g : Polynomial R) (m : ℕ), f.resul
tant g 0 m = f.coeff 0 ^ m
参数：f g : Polynomial R；m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Polynomial.sylvester_zero_left_deg`：∀ {R : Type u_1} [inst : Semiring R]
 (f g : Polynomial R) (m : ℕ),   f.sylvester g 0 m = Matrix.diagonal fun x => f.
coeff 0
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem resultant_zero_left_deg : resultant f g 0 m = f.coeff 0 ^ m := by
  simp [resultant]

/-- For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`. -/
/-
**Polynomial.resultant_C_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：resultant_C_zero_left : resultant (C r) g 0 m = r ^ m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`.
-/
theorem resultant_C_zero_left : resultant (C r) g 0 m = r ^ m := by simp

set_option backward.defeqAttrib.useBackward true in
/-- `Res(f, g) = (-1)ᵐⁿ Res(g, f)` -/
/-
**Polynomial.resultant_comm** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_comm : resultant f g m n = (-1) ^ (m * n) * resultant g f n m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (f g : P
olynomial R) (m n : ℕ), f.resultant g m n = (f.sylvester g m n).det
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Polynomial.sylvester_comm`：sylvester_comm : sylvester f g m n = (sylvest
er g f n m).reindex (finCongr (add_comm n m)) (finSumFinEquiv.symm.trans <| (Equ
iv.sumComm _ _)…
· 使用引理 `Matrix.det_reindex`：det_reindex (e e' : m ≃ n) (M : Matrix m m R) : (M.r
eindex e e').det = sign (e'.trans e.symm) * M.det
· 使用定理 `Equiv.Perm.sign_eq_prod_prod_Ioi`：Equiv.Perm.sign_eq_prod_prod_Ioi (σ : 
Equiv.Perm (Fin n)) : σ.sign = ∏ i, ∏ j in Finset.Ioi i, (if σ i < σ j then 1 el
se -1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Units.coe_prod`：Units.coe_prod [CommMonoid M] (f : α -> Mˣ) (s : Finset 
α) : (↑(∏ i in s, f i) : M) = ∏ i in s, (f i : M)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Int.cast_prod`：cast_prod {R : Type*} [CommRing R] (f : ι -> Int) (s : Fi
nset ι) : (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Finset.prod_map_equiv`：prod_map_equiv (e : ι ≃ κ) : (s.map e).prod (f ∘ 
e.symm) = s.prod f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用引理 `Finset.prod_ite_mem_eq`：prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : 
ι -> M) [DecidablePred (· in s)] : (∏ i, if i in s then f i else 1) = ∏ i in s, 
f i
· 使用定理 `Fintype.prod_sum_type`：Fintype.prod_sum_type (f : α₁ oplus α₂ -> M) : ∏ 
x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
`Res(f, g) = (-1)ᵐⁿ Res(g, f)`
-/
lemma resultant_comm : resultant f g m n = (-1) ^ (m * n) * resultant g f n m := by
  rw [resultant, resultant, sylvester_comm, Matrix.det_reindex, Equiv.Perm.sign_eq_prod_prod_Ioi]
  congr 1
  dsimp
  simp only [Fin.cast_lt_cast, Units.coe_prod, apply_ite, Units.val_one, Units.val_neg,
    Int.reduceNeg, Int.cast_prod, Int.cast_one, Int.cast_neg]
  simp_rw [← finSumFinEquiv.prod_comp, ← Finset.prod_map_equiv finSumFinEquiv.symm]
  simp only [Equiv.symm_apply_apply, ← Fin.val_fin_lt, Equiv.symm_symm, Function.comp_apply,
    ← Finset.prod_ite_mem_eq (Finset.map _ _), Finset.mem_map_equiv, Finset.mem_Ioi,
    Fintype.prod_sum_type, finSumFinEquiv_apply_left, Fin.val_castAdd, Sum.swap_inl,
    finSumFinEquiv_apply_right, Fin.val_natAdd, Sum.swap_inr, add_lt_add_iff_left,
    ← ite_not (α := R) (p := _ < _) (y := 1), ← ite_and, and_not_self]
  simp [(Fin.isLt _).trans_le, (Fin.isLt _).le.trans, pow_mul]
/-
**Polynomial.resultant_zero_right_deg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (f g : Polynomial R) (m : ℕ), f.resul
tant g m 0 = g.coeff 0 ^ m
参数：f g : Polynomial R；m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem resultant_zero_right_deg : resultant f g m 0 = g.coeff 0 ^ m := by
  rw [resultant_comm]; simp

/-- `Res(a, g) = a ^ deg g` -/
/-
**Polynomial.resultant_C_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：resultant_C_zero_right (r : R) : resultant f (C r) m 0 = r ^ m
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant_zero_right_deg`：∀ {R : Type u_1} [inst : CommRing R
] (f g : Polynomial R) (m : ℕ), f.resultant g m 0 = g.coeff 0 ^ m
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Res(a, g) = a ^ deg g`
-/
theorem resultant_C_zero_right (r : R) : resultant f (C r) m 0 = r ^ m := by simp

@[simp]
/-
**Polynomial.resultant_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：resultant_zero_right : resultant f 0 m n = 0 ^ m * f.coeff 0 ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `instNeZeroNatHAdd`：∀ {n m : ℕ} [h : NeZero n], NeZero (n + m)
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Matrix.det_eq_zero_of_column_eq_zero`：det_eq_zero_of_column_eq_zero {A :
 Matrix n n R} (j : n) (h : forall i, A i j = 0) : det A = 0
-/
theorem resultant_zero_right : resultant f 0 m n = 0 ^ m * f.coeff 0 ^ n := by
  obtain _ | m := m; · simp
  have (i : Fin (m + 1 + n)) : sylvester f 0 (m + 1) n i ⟨0, by lia⟩ = 0 := by
    simp [sylvester, show (0 : Fin (m + 1 + n)) = Fin.castAdd _ 0 from rfl, Fin.addCases_left]
  simpa [resultant] using Matrix.det_eq_zero_of_column_eq_zero ⟨0, by lia⟩ this

@[simp]
/-
**Polynomial.resultant_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：resultant_zero_left : resultant 0 g m n = 0 ^ n * g.coeff 0 ^ m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用定理 `Polynomial.resultant_zero_right`：resultant_zero_right : resultant f 0 m 
n = 0 ^ m * f.coeff 0 ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem resultant_zero_left : resultant 0 g m n = 0 ^ n * g.coeff 0 ^ m := by
  rw [resultant_comm, resultant_zero_right]
  cases n <;> simp
/-
**Polynomial.resultant_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：resultant_zero_zero : resultant (0 : R[X]) 0 m n = 0 ^ (m + n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant_zero_right`：resultant_zero_right : resultant f 0 m 
n = 0 ^ m * f.coeff 0 ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem resultant_zero_zero : resultant (0 : R[X]) 0 m n = 0 ^ (m + n) := by simp [pow_add]

/-- See `resultant_add_mul_right`. -/
/-
**Polynomial.resultant_add_mul_monomial_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `resultant_add_mul_right`.
-/
private lemma resultant_add_mul_monomial_right (hk : k + m ≤ n) (hf : f.natDegree ≤ m) :
    resultant f (g + f * monomial k r) m n = resultant f g m n := by
  obtain rfl | hm := eq_or_ne m 0
  · obtain ⟨q, rfl⟩ := natDegree_eq_zero.mp (le_zero_iff.mp hf); simp
  let M₁ := f.sylvester (g + f * monomial k r) m n
  let M₂ := f.sylvester g m n
  let M (i : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
    .of fun j₁ j₂ ↦ if j₂.1 < i then M₁ j₁ j₂ else M₂ j₁ j₂
  have (i : ℕ) (hi : i ≤ m) : (M i).det = M₂.det := by
    induction i with
    | zero => simp [M]; rfl
    | succ i IH =>
      rw [← IH (by lia), ← Matrix.det_updateCol_add_smul_self (i := ⟨i, by lia⟩)
        (j := ⟨i + k + m, by lia⟩) (c := -r) (M (i + 1)) (by simp; lia)]
      congr 1
      ext j₁ j₂
      simp only [Matrix.of_apply, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, add_assoc,
        add_lt_add_iff_left, Nat.lt_one_iff, Nat.add_eq_zero_iff, hm, and_false, smul_eq_mul,
        Matrix.updateCol_apply, Fin.ext_iff, M, M₂, neg_mul, ← sub_eq_add_neg]
      obtain rfl | h := eq_or_ne ↑j₂ i
      · simp only [↓reduceIte, sylvester, Set.mem_Icc, coeff_add, Fin.eta, Matrix.of_apply,
          lt_self_iff_false, M₁]
        induction j₂ using Fin.addCases with
        | left j₂ =>
          dsimp at hi
          have : Fin.mk (n := m + n) (↑j₂ + (k + m)) (by lia) = .natAdd m ⟨j₂ + k, by lia⟩ :=
            Fin.ext (by simp; lia)
          simp only [Fin.addCases_left, Fin.val_castAdd, this, Fin.addCases_right, mul_ite,
            mul_zero, ← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', ite_add_zero,
            coeff_mul_C, add_assoc, add_eq_left, ← ite_and, ← mul_comm r, tsub_add_eq_tsub_tsub,
            add_sub_assoc, sub_eq_zero]
          split_ifs with h₁ h₂ h₂ <;> try rfl
          · rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
            exact hf.trans_lt (by lia)
          · lia
        | right i =>
          simp only [Fin.val_natAdd] at hi
          have : Fin.mk (n := m + n) (m + ↑i + (k + m)) (by lia) =
              Fin.natAdd m ⟨↑i + (k + m), by lia⟩ := Fin.ext (by simp; lia)
          simp only [Fin.addCases_right, Fin.val_natAdd, sub_eq_self, this]
          rw [if_neg, mul_zero]
          lia
      lia
  rw [resultant, resultant, ← this m le_rfl]
  congr 1
  ext i j
  induction j using Fin.addCases <;> simp [M, sylvester, M₁, M₂]

set_option backward.defeqAttrib.useBackward true in
/-- `Res(f, g + fp) = Res(f, g)` if `deg f + deg p ≤ deg g`. -/
/-
**Polynomial.resultant_add_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_add_mul_right (hp : p.natDegree + m <= n) (hf : f.natDegree <= m
) : resultant f (g + f * p) m n = resultant f g m n
参数：hp : p.natDegree + m <= n；hf : f.natDegree <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
· 使用定理 `Polynomial.sum_eq_of_subset`：sum_eq_of_subset {S : Type*} [AddCommMonoid
 S] {p : R[X]} (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) {s : Finset Nat} (
hs : p.support su…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.Resultant.Basic.0.Polynomial.resu
ltant_add_mul_monomial_right`：∀ {R : Type u_1} [inst : CommRing R] (f g : Polyno
mial R) (r : R) (m n k : ℕ),   k + m ≤ n → f.natDegree ≤ m → f.resultant (g + f 
* (Polynom…

--- 原说明 ---
`Res(f, g + fp) = Res(f, g)` if `deg f + deg p ≤ deg g`.
-/
lemma resultant_add_mul_right (hp : p.natDegree + m ≤ n) (hf : f.natDegree ≤ m) :
    resultant f (g + f * p) m n = resultant f g m n := by
  have H : p.support ⊆ Finset.range (n - m + 1) := by
    simp only [Finset.subset_iff, Finset.mem_range]
    exact fun x hx ↦ (le_natDegree_of_mem_supp _ hx).trans_lt (by lia)
  rw [← p.sum_monomial_eq, Polynomial.sum_eq_of_subset _ (by simp) H]
  set k := n - m + 1
  replace H := show k ≤ n - m + 1 from le_rfl
  clear_value k
  induction k generalizing g with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [mul_zero, add_zero]
  | succ k IH =>
    rw [Finset.sum_range_succ, mul_add, ← add_assoc, resultant_add_mul_monomial_right, IH] <;> lia

/-- `Res(f + gp, g) = Res(f, g)` if `deg g + deg p ≤ deg f`. -/
/-
**Polynomial.resultant_add_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_add_mul_left (hk : p.natDegree + n <= m) (hg : g.natDegree <= n)
 : resultant (f + g * p) g m n = resultant f g m n
参数：hk : p.natDegree + n <= m；hg : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用引理 `Polynomial.resultant_add_mul_right`：resultant_add_mul_right (hp : p.natD
egree + m <= n) (hf : f.natDegree <= m) : resultant f (g + f * p) m n = resultan
t f g m n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_pow`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ ℕ → α} {a : α} {b : ℕ} {a' : ℤ} {b' : ℕ} {c : ℤ},   f = HPow.hPow →     Mathli
b.Meta.NormNum.IsInt…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
`Res(f + gp, g) = Res(f, g)` if `deg g + deg p ≤ deg f`.
-/
lemma resultant_add_mul_left (hk : p.natDegree + n ≤ m) (hg : g.natDegree ≤ n) :
    resultant (f + g * p) g m n = resultant f g m n := by
  rw [resultant_comm, resultant_add_mul_right _ _ _ _ _ hk hg, resultant_comm,
    ← mul_assoc, ← pow_add, mul_comm m n, ← two_mul, pow_mul]
  ring

/-- `Res(f, a • g) = a ^ {deg f} * Res(f, g)`. -/
/-
**Polynomial.resultant_C_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_C_mul_right (r : R) : resultant f (C r * g) m n = r ^ m * result
ant f g m n
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Matrix.updateCol.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq n} [inst_1 : DecidableEq n] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (j j_…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Matrix.updateCol_apply`：updateCol_apply [DecidableEq n] {j' : n} : updat
eCol M j c i j' = if j' = j then c i else M i j'
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.sylvester.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f g : P
olynomial R) (m n : ℕ),   f.sylvester g m n =     Matrix.of fun i j =>       Fin
.addCases (fun …
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
`Res(f, a • g) = a ^ {deg f} * Res(f, g)`.
-/
lemma resultant_C_mul_right (r : R) :
    resultant f (C r * g) m n = r ^ m * resultant f g m n := by
  let M₁ := f.sylvester (C r * g) m n
  let M₂ := f.sylvester g m n
  let M (i : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
    .of fun j₁ j₂ ↦ if j₂.1 < i then M₁ j₁ j₂ else M₂ j₁ j₂
  have (i : ℕ) (hi : i ≤ m) : (M i).det = r ^ i * M₂.det := by
    induction i with
    | zero => simp [M]; rfl
    | succ i IH =>
      suffices (M i).updateCol ⟨i, by lia⟩ (r • fun j ↦ M i j ⟨i, by lia⟩) = (M (i + 1)) by
        rw [pow_succ', mul_assoc, ← IH (by lia), ← this, Matrix.det_updateCol_smul,
          Matrix.updateCol_eq_self]
      ext j₁ j₂
      simp only [Matrix.of_apply, lt_self_iff_false, ↓reduceIte, Matrix.updateCol_apply,
        Fin.ext_iff, Pi.smul_apply, smul_eq_mul, M, M₂]
      obtain rfl | h := eq_or_ne ↑j₂ i
      · simp only [↓reduceIte, sylvester, Set.mem_Icc, Fin.eta, Matrix.of_apply,
          lt_add_iff_pos_right, zero_lt_one, coeff_C_mul, M₁]
        induction j₂ using Fin.addCases with
        | left j₂ => simp
        | right i => simp at hi
      lia
  rw [resultant, resultant, ← this m le_rfl]
  congr 1
  ext i j
  induction j using Fin.addCases <;> simp [M, sylvester, M₁, M₂]

/-- `Res(a • f, g) = a ^ {deg g} * Res(f, g)`. -/
/-
**Polynomial.resultant_C_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_C_mul_left (r : R) : resultant (C r * f) g m n = r ^ n * resulta
nt f g m n
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用引理 `Polynomial.resultant_C_mul_right`：resultant_C_mul_right (r : R) : result
ant f (C r * g) m n = r ^ m * resultant f g m n
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
`Res(a • f, g) = a ^ {deg g} * Res(f, g)`.
-/
lemma resultant_C_mul_left (r : R) :
    resultant (C r * f) g m n = r ^ n * resultant f g m n := by
  rw [resultant_comm, resultant_C_mul_right, resultant_comm, mul_left_comm, ← mul_assoc ((-1) ^ _),
    mul_comm n m, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
/-
**Polynomial.resultant_succ_left_deg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_succ_left_deg (hf : f.natDegree <= m) : resultant f g (m + 1) n 
= (-1) ^ n * g.coeff n * resultant f g m n
参数：hf : f.natDegree <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant_zero_right_deg`：∀ {R : Type u_1} [inst : CommRing R
] (f g : Polynomial R) (m : ℕ), f.resultant g m 0 = g.coeff 0 ^ m
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.resultant.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (f g : P
olynomial R) (m n : ℕ), f.resultant g m n = (f.sylvester g m n).det
· 使用定理 `Matrix.det_succ_row`：det_succ_row {n : Nat} (A : Matrix (Fin n.succ) (Fi
n n.succ) R) (i : Fin n.succ) : det A = ∑ j : Fin n.succ, (-1) ^ (i + j : Nat) *
 A i j * …
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 59 条，此处仅展示前 30 条）
-/
lemma resultant_succ_left_deg (hf : f.natDegree ≤ m) :
    resultant f g (m + 1) n = (-1) ^ n * g.coeff n * resultant f g m n := by
  obtain _ | n := n
  · simp [pow_succ']
  rw [resultant, Matrix.det_succ_row (i := .last _),
      Finset.sum_eq_single (by exact ((Fin.last m).castAdd (n + 1))) _ (by simp)]
  · rw [resultant, ← Matrix.det_reindex_self (finCongr (show (m + 1).add n = m + (n + 1) by grind))]
    simp only [Nat.add_eq, Nat.succ_eq_add_one, Fin.val_last, Fin.val_castAdd, Fin.succAbove_last,
      Matrix.reindex_apply, finCongr_symm, Matrix.submatrix_submatrix]
    congr 2
    · trans (-1) ^ (2 * m + (n + 1))
      · congr 1; lia
      · simp [pow_add]
    · simp only [sylvester, Set.mem_Icc, Matrix.of_apply, Fin.val_last, Fin.addCases_left]
      rw [if_pos (by lia)]
      simp [add_assoc, add_comm 1]
    · ext i j
      simp only [sylvester, Set.mem_Icc, Matrix.submatrix_apply, Function.comp_apply,
        finCongr_apply, Matrix.of_apply, Fin.val_castSucc, Fin.val_cast]
      induction j using Fin.addCases with
      | left j =>
        have : ((Fin.last m).castAdd (n + 1)).succAbove ((j.castAdd (n + 1)).cast (by grind)) =
          j.castSucc.castAdd (n + 1) := by ext; simp [Fin.succAbove, Fin.lt_def]
        simp [this]
      | right j =>
        have : ((Fin.last m).castAdd (n + 1)).succAbove ((j.natAdd m).cast (by grind)) =
          j.natAdd _ := by ext; simp [Fin.succAbove, Fin.lt_def, add_right_comm]
        simp only [ite_and, this, Fin.addCases_right]
        split_ifs with h₁ h₂ h₃ h₃ <;> try lia
        exact coeff_eq_zero_of_natDegree_lt (by lia)
  · rintro (b : Fin ((m + 1) + (n + 1))) - hb
    suffices f.sylvester g (m + 1) (n + 1) (.last (m + 1 + n)) b = 0 by simp [this]
    induction b using Fin.addCases with
    | left b =>
      simp only [Nat.add_eq, Nat.succ_eq_add_one, ne_eq, Fin.ext_iff, Fin.val_castAdd,
        Fin.val_last] at hb
      simp only [sylvester, Set.mem_Icc, Matrix.of_apply, Fin.val_last, Fin.addCases_left,
        ite_eq_right_iff, and_imp]
      intros
      lia
    | right i => simpa [sylvester] using fun _ _ ↦ coeff_eq_zero_of_natDegree_lt (by lia)
/-
**Polynomial.resultant_add_left_deg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_add_left_deg (hf : f.natDegree <= m) : resultant f g (m + k) n =
 (-1) ^ (n * k) * g.coeff n ^ k * resultant f g m n
参数：hf : f.natDegree <= m。
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Polynomial.resultant_succ_left_deg`：resultant_succ_left_deg (hf : f.natD
egree <= m) : resultant f g (m + 1) n = (-1) ^ n * g.coeff n * resultant f g m n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 54 条，此处仅展示前 30 条）
-/
lemma resultant_add_left_deg (hf : f.natDegree ≤ m) :
    resultant f g (m + k) n = (-1) ^ (n * k) * g.coeff n ^ k * resultant f g m n := by
  induction k with
  | zero => simp
  | succ k IH => simp [← add_assoc, resultant_succ_left_deg, hf.trans, IH]; ring
/-
**Polynomial.resultant_add_right_deg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_add_right_deg (k : Nat) (hg : g.natDegree <= n) : resultant f g 
m (n + k) = f.coeff m ^ k * resultant f g m n
参数：k : Nat；hg : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用引理 `Polynomial.resultant_add_left_deg`：resultant_add_left_deg (hf : f.natDeg
ree <= m) : resultant f g (m + k) n = (-1) ^ (n * k) * g.coeff n ^ k * resultant
 f g m n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 59 条，此处仅展示前 30 条）
-/
lemma resultant_add_right_deg (k : ℕ) (hg : g.natDegree ≤ n) :
    resultant f g m (n + k) = f.coeff m ^ k * resultant f g m n := by
  rw [resultant_comm, resultant_add_left_deg _ _ _ _ _ hg, resultant_comm,
    mul_assoc, mul_left_comm (f.coeff m ^ k)]
  simp only [← mul_assoc, ← pow_add, ← mul_add, mul_comm _ m]
  ring_nf
  simp [mul_comm]
/-
**Polynomial.resultant_eq_zero_of_lt_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_eq_zero_of_lt_lt (hf : f.natDegree < m) (hg : g.natDegree < n) :
 resultant f g m n = 0
参数：hf : f.natDegree < m；hg : g.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_add_left_deg`：resultant_add_left_deg (hf : f.natDeg
ree <= m) : resultant f g (m + k) n = (-1) ^ (n * k) * g.coeff n ^ k * resultant
 f g m n
· 使用引理 `Polynomial.resultant_add_right_deg`：resultant_add_right_deg (k : Nat) (h
g : g.natDegree <= n) : resultant f g m (n + k) = f.coeff m ^ k * resultant f g 
m n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resultant_eq_zero_of_lt_lt (hf : f.natDegree < m) (hg : g.natDegree < n) :
    resultant f g m n = 0 := by
  obtain _ | m := m; · lia
  obtain _ | n := n; · lia
  rw [resultant_add_left_deg _ _ _ _ _ (by lia), resultant_add_right_deg _ _ _ _ _ (by lia)]
  simp [coeff_eq_zero_of_natDegree_lt hg]

@[simp]
/-
**Polynomial.resultant_C_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：resultant_C_left (r : R) : resultant (C r) g m n = (-1) ^ (m * n) * g.coef
f n ^ m * r ^ n
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Polynomial.resultant_add_left_deg`：resultant_add_left_deg (hf : f.natDeg
ree <= m) : resultant f g (m + k) n = (-1) ^ (n * k) * g.coeff n ^ k * resultant
 f g m n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem resultant_C_left (r : R) :
    resultant (C r) g m n = (-1) ^ (m * n) * g.coeff n ^ m * r ^ n := by
  rw [← zero_add m, resultant_add_left_deg _ _ _ _ _ (by simp), mul_comm n m]
  simp
/-
**Polynomial.resultant_C_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (f : Polynomial R) (m n : ℕ) (r : R),
   f.resultant (Polynomial.C r) m n = f.coeff m ^ n * r ^ m
参数：f : Polynomial R；m n : ℕ；r : R；Polynomial.C r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Polynomial.resultant_add_right_deg`：resultant_add_right_deg (k : Nat) (h
g : g.natDegree <= n) : resultant f g m (n + k) = f.coeff m ^ k * resultant f g 
m n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.resultant_zero_right_deg`：∀ {R : Type u_1} [inst : CommRing R
] (f g : Polynomial R) (m : ℕ), f.resultant g m 0 = g.coeff 0 ^ m
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem resultant_C_right (r : R) : resultant f (C r) m n = f.coeff m ^ n * r ^ m := by
  rw [← zero_add n, resultant_add_right_deg _ _ _ _ _ (by simp)]
  simp
/-
**Polynomial.resultant_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (g : Polynomial R) (m n : ℕ),   Polyn
omial.resultant 1 g m n = (-1) ^ (m * n) * g.coeff n ^ m
参数：g : Polynomial R；m n : ℕ；-1；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.resultant_C_left`：resultant_C_left (r : R) : resultant (C r) 
g m n = (-1) ^ (m * n) * g.coeff n ^ m * r ^ n
-/
@[simp] theorem resultant_one_left : resultant 1 g m n = (-1) ^ (m * n) * g.coeff n ^ m := by
  simpa [-resultant_C_left] using! resultant_C_left g m n 1
/-
**Polynomial.resultant_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (f : Polynomial R) (m n : ℕ), f.resul
tant 1 m n = f.coeff m ^ n
参数：f : Polynomial R；m n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.resultant_C_right`：∀ {R : Type u_1} [inst : CommRing R] (f : 
Polynomial R) (m n : ℕ) (r : R),   f.resultant (Polynomial.C r) m n = f.coeff m 
^ n * r ^ m
-/
@[simp] theorem resultant_one_right : resultant f 1 m n = f.coeff m ^ n := by
  simpa [-resultant_C_right] using! resultant_C_right f m n 1

/-- `Res(X - r, g) = g(r)` -/
/-
**Polynomial.resultant_X_sub_C_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (g : Polynomial R) (n : ℕ) (r : R),  
 g.natDegree ≤ n → (Polynomial.X - Polynomial.C r).resultant g 1 n = Polynomial.
eval r g
参数：g : Polynomial R；n : ℕ；r : R；Polynomial.X - Polynomial.C r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant_C_right`：∀ {R : Type u_1} [inst : CommRing R] (f : 
Polynomial R) (m n : ℕ) (r : R),   f.resultant (Polynomial.C r) m n = f.coeff m 
^ n * r ^ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用引理 `Polynomial.resultant_add_mul_right`：resultant_add_mul_right (hp : p.natD
egree + m <= n) (hf : f.natDegree <= m) : resultant f (g + f * p) m n = resultan
t f g m n
· 使用定理 `Polynomial.natDegree_divByMonic`：natDegree_divByMonic (f : R[X]) {g : R[
X]} (hg : g.Monic) : natDegree (f /ₘ g) = natDegree f - natDegree g
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Polynomial.natDegree_X_sub_C_le`：natDegree_X_sub_C_le (r : R) : (X - C r
).natDegree <= 1
· 使用定理 `Polynomial.modByMonic_X_sub_C_eq_C_eval`：modByMonic_X_sub_C_eq_C_eval (p
 : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a)

--- 原说明 ---
`Res(X - r, g) = g(r)`
-/
@[simp] lemma resultant_X_sub_C_left (r : R) (hg : g.natDegree ≤ n) :
    (X - C r).resultant g 1 n = eval r g := by
  nontriviality R
  obtain hg | hg := g.natDegree.eq_zero_or_pos
  · obtain ⟨s, rfl⟩ := natDegree_eq_zero.mp hg
    simp
  conv_lhs => rw [← g.modByMonic_add_div (X - C r)]
  rw [resultant_add_mul_right _ _ _ _ _ _ (natDegree_X_sub_C_le _), modByMonic_X_sub_C_eq_C_eval]
  · simp
  · rw [natDegree_divByMonic g (monic_X_sub_C r), natDegree_sub_C, natDegree_X]
    lia

/-- `Res(X + r, g) = g(-r)` -/
/-
**Polynomial.resultant_X_add_C_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (g : Polynomial R) (n : ℕ) (r : R),  
 g.natDegree ≤ n → (Polynomial.X + Polynomial.C r).resultant g 1 n = Polynomial.
eval (-r) g
参数：g : Polynomial R；n : ℕ；r : R；Polynomial.X + Polynomial.C r；-r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.resultant_X_sub_C_left`：∀ {R : Type u_1} [inst : CommRing R] 
(g : Polynomial R) (n : ℕ) (r : R),   g.natDegree ≤ n → (Polynomial.X - Polynomi
al.C r).resultant g 1 n…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b

--- 原说明 ---
`Res(X + r, g) = g(-r)`
-/
@[simp] lemma resultant_X_add_C_left (r : R) (hg : g.natDegree ≤ n) :
    (X + C r).resultant g 1 n = eval (-r) g := by
  rw [← resultant_X_sub_C_left g n (-r) hg, map_neg, sub_neg_eq_add]

/-- `Res(f, X - r) = (-1)^{deg f} * f(r)` -/
/-
**Polynomial.resultant_X_sub_C_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (f : Polynomial R) (m : ℕ) (r : R),  
 f.natDegree ≤ m → f.resultant (Polynomial.X - Polynomial.C r) m 1 = (-1) ^ m * 
Polynomial.eval r f
参数：f : Polynomial R；m : ℕ；r : R；Polynomial.X - Polynomial.C r；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用定理 `Polynomial.resultant_X_sub_C_left`：∀ {R : Type u_1} [inst : CommRing R] 
(g : Polynomial R) (n : ℕ) (r : R),   g.natDegree ≤ n → (Polynomial.X - Polynomi
al.C r).resultant g 1 n…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Res(f, X - r) = (-1)^{deg f} * f(r)`
-/
@[simp] lemma resultant_X_sub_C_right (r : R) (hf : f.natDegree ≤ m) :
    f.resultant (X - C r) m 1 = (-1) ^ m * eval r f := by
  rw [resultant_comm, resultant_X_sub_C_left _ _ _ hf]
  simp

/-- `Res(f, X + r) = (-1)^{deg f} * f(-r)` -/
/-
**Polynomial.resultant_X_add_C_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (f : Polynomial R) (m : ℕ) (r : R),  
 f.natDegree ≤ m → f.resultant (Polynomial.X + Polynomial.C r) m 1 = (-1) ^ m * 
Polynomial.eval (-r) f
参数：f : Polynomial R；m : ℕ；r : R；Polynomial.X + Polynomial.C r；-1；-r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.resultant_X_sub_C_right`：∀ {R : Type u_1} [inst : CommRing R]
 (f : Polynomial R) (m : ℕ) (r : R),   f.natDegree ≤ m → f.resultant (Polynomial
.X - Polynomial.C r) m 1…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b

--- 原说明 ---
`Res(f, X + r) = (-1)^{deg f} * f(-r)`
-/
@[simp] lemma resultant_X_add_C_right (r : R) (hf : f.natDegree ≤ m) :
    f.resultant (X + C r) m 1 = (-1) ^ m * eval (-r) f := by
  rw [← resultant_X_sub_C_right f m (-r) hf, map_neg, sub_neg_eq_add]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` and `g` are monic and splits, then `Res(f, g) = ∏ (α - β)`,
where `α` and `β` runs through the roots of `f` and `g` respectively. -/
/-
**Polynomial.resultant_eq_prod_roots_sub** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_eq_prod_roots_sub {K : Type*} [Field K] (f g : K[X]) (hf : f.Mon
ic) (hg : g.Monic) (hf' : f.Splits) (hg' : g.Splits) : resultant f g = ((f.roots
 ×ˢ g.roots).map fun ij => ij.1 - ij.2).prod
参数：f g : K[X]；hf : f.Monic；hg : g.Monic；hf' : f.Splits；hg' : g.Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.resultant_add_mul_left`：resultant_add_mul_left (hk : p.natDeg
ree + n <= m) (hg : g.natDegree <= n) : resultant (f + g * p) g m n = resultant 
f g m n
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Polynomial.resultant_zero_left`：resultant_zero_left : resultant 0 g m n 
= 0 ^ n * g.coeff 0 ^ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
（共 120 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` and `g` are monic and splits, then `Res(f, g) = ∏ (α - β)`,
where `α` and `β` runs through the roots of `f` and `g` respectively.
-/
lemma resultant_eq_prod_roots_sub
    {K : Type*} [Field K] (f g : K[X]) (hf : f.Monic) (hg : g.Monic)
    (hf' : f.Splits) (hg' : g.Splits) :
    resultant f g = ((f.roots ×ˢ g.roots).map fun ij ↦ ij.1 - ij.2).prod := by
  wlog hfg : g.natDegree ≤ f.natDegree
  · trans ((f.roots ×ˢ g.roots).map fun ij ↦ (-1) * (ij.2 - ij.1)).prod
    · rw [resultant_comm, this g f hg hf hg' hf' (le_of_not_ge hfg), ← Multiset.map_swap_product,
        Multiset.map_map, Multiset.prod_map_mul]
      simp [hf'.natDegree_eq_card_roots, hg'.natDegree_eq_card_roots]
    · simp
  generalize hN : f.natDegree + g.natDegree = N
  induction N using Nat.strong_induction_on generalizing K with | h n IH =>
  by_cases hr : g ∣ f
  · obtain ⟨r, rfl⟩ := hr
    have hr' : r ≠ 0 := by simpa [hg.ne_zero] using hf.ne_zero
    rw [← resultant_add_mul_left _ _ (-r) _ _ _ le_rfl]
    · rw [mul_neg, add_neg_cancel, resultant_zero_left]
      by_cases H : g.natDegree = 0
      · obtain rfl := hg.natDegree_eq_zero.mp H
        simp
      · simp only [zero_pow H]
        rw [hg'.natDegree_eq_card_roots, Multiset.card_eq_zero,
          Multiset.eq_zero_iff_forall_notMem, not_forall_not] at H
        obtain ⟨x, hx⟩ := H
        rw [Multiset.prod_eq_zero, zero_mul]
        simp only [Multiset.mem_map, Prod.exists]
        exact ⟨x, x, Multiset.mem_product.mpr (by simp_all [hg.ne_zero]), by simp⟩
    · rw [natDegree_mul hg.ne_zero (by simpa [hg.ne_zero] using hf.ne_zero),
        natDegree_neg, add_comm]
  let r := C (f %ₘ g).leadingCoeff⁻¹ * (f %ₘ g)
  have hr₀ : f %ₘ g ≠ 0 := by simpa [modByMonic_eq_zero_iff_dvd, hg]
  have hrd : r.natDegree < g.natDegree := by
    simp [r, natDegree_C_mul, hr₀, natDegree_modByMonic_lt _ hg (show g ≠ 1 by aesop)]
  have hr : r.Monic := by
    dsimp only [r]
    rw [Monic, leadingCoeff, natDegree_C_mul (by simpa), coeff_C_mul, leadingCoeff,
      inv_mul_cancel₀ (by simpa)]
  let L := r.SplittingField
  have := IH _ (by simp; lia)
    (g.map (algebraMap K L)) (r.map (algebraMap K L)) (hg.map _) (hr.map _)
    (hg'.map _) (SplittingField.splits _) (by simpa [r, natDegree_C_mul, hr₀] using hrd.le) rfl
  rw [resultant_map_map, natDegree_map, natDegree_map, resultant_C_mul_right,
    map_mul, inv_pow, map_inv₀, inv_mul_eq_iff_eq_mul₀ (by simp [hr₀])] at this
  rw [← f.modByMonic_add_div, resultant_add_mul_left, f.modByMonic_add_div,
    ← Nat.sub_add_cancel (hrd.le.trans hfg), add_comm, resultant_add_left_deg, resultant_comm]
  · apply (algebraMap K L).injective
    rw [map_mul, map_mul, map_mul, this, map_sub_roots_sprod_eq_prod_map_eval _ _ hf hf',
      map_sub_sprod_roots_eq_prod_map_eval _ _ (hr.map _) (SplittingField.splits _), map_mul,
      hg'.roots_map]
    have : (g.roots.map (eval · f)).prod =
        (f %ₘ g).leadingCoeff ^ g.natDegree * (g.roots.map (eval · r)).prod := by
      trans (g.roots.map ((f %ₘ g).leadingCoeff * eval · r)).prod
      · congr 1
        refine Multiset.map_congr rfl ?_
        simp only [mem_roots', ne_eq, IsRoot.def, eval_mul, eval_C, leadingCoeff_eq_zero, hr₀,
          not_false_eq_true, mul_inv_cancel_left₀, and_imp, r]
        intro x hx hxg
        conv_lhs => rw [← f.modByMonic_add_div, eval_add, eval_mul, hxg, zero_mul, add_zero]
      · simp [hg'.natDegree_eq_card_roots]
    simp only [coeff_natDegree, hg.leadingCoeff, one_pow, map_one, map_multiset_prod,
      ← hf'.natDegree_eq_card_roots, ← hg'.natDegree_eq_card_roots, this, map_mul, Multiset.map_map,
      map_pow, map_neg, mul_one, eval_map_algebraMap, Function.comp_apply]
    simp only [← mul_assoc, ← pow_add, ← add_mul, Nat.sub_add_cancel (hrd.le.trans hfg),
      mul_comm g.natDegree]
    congr 3 with x
    exact aeval_algebraMap_apply _ _ _
  · simp [r, hr₀, natDegree_C_mul]
  · rw [f.modByMonic_add_div, natDegree_divByMonic _ hg, Nat.sub_add_cancel hfg]
  · simp

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` splits with leading coeff `a` and degree `n`,
then `Res(f, g) = aⁿ * ∏ g(α)` where `α` runs through the roots of `f`. -/
nonrec lemma resultant_eq_prod_eval [IsDomain R]
    (f g : R[X]) (n : ℕ) (hg : g.natDegree ≤ n) (hf : f.Splits) :
    resultant f g f.natDegree n = f.leadingCoeff ^ n * (f.roots.map g.eval).prod := by
  wlog hR : IsField R
  · let K := FractionRing R
    apply FaithfulSMul.algebraMap_injective R K
    have := this (f.map (algebraMap R K)) (g.map (algebraMap R K)) n (natDegree_map_le.trans hg)
      (hf.map _) (Field.toIsField _)
    simp only [resultant_map_map, natDegree_map_eq_of_injective, leadingCoeff_map_of_injective,
      FaithfulSMul.algebraMap_injective R K, ← hf.natDegree_eq_card_roots,
      ← roots_map_of_injective_of_card_eq_natDegree] at this
    simpa [map_multiset_prod, aeval_algebraMap_apply, Multiset.map_map] using this
  by_cases hf0 : f = 0
  · simp [hf0]
  wlog hfm : f.Monic
  · let inst := hR.toField
    have H : (C f.leadingCoeff⁻¹ * f).Monic := by
      rw [Monic, ← coeff_natDegree, natDegree_C_mul (by simp [hf0]), coeff_C_mul]; simp [hf0]
    have := this (C f.leadingCoeff⁻¹ * f) g n hg (.mul (.C _) hf) hR (by simpa) H
    simpa [hf0, natDegree_C_mul, resultant_C_mul_left, inv_mul_eq_iff_eq_mul₀, roots_C_mul,
      H.leadingCoeff] using this
  simp only [hfm.leadingCoeff, one_pow, one_mul]
  clear hf0
  by_cases hg0 : g = 0
  · subst hg0
    by_cases hf' : f.natDegree = 0
    · obtain ⟨r, rfl⟩ := hfm.natDegree_eq_zero.mp hf'; simp
    simp [← hf.natDegree_eq_card_roots, hf']
  wlog hgm : g.Monic
  · let inst := hR.toField
    have := this f (C g.leadingCoeff⁻¹ * g) n (by simpa [hg0, natDegree_C_mul]) hf hR hfm (by simpa)
      (by rw [Monic, ← coeff_natDegree, natDegree_C_mul (by simp [hg0]), coeff_C_mul]; simp [hg0])
    rw [resultant_C_mul_right, inv_pow, inv_mul_eq_iff_eq_mul₀ (by simp [hg0])] at this
    simpa [← hf.natDegree_eq_card_roots, inv_pow, mul_left_comm (_ ^ g.natDegree), hg0] using this
  let inst := hR.toField
  let L := g.SplittingField
  apply (algebraMap R L).injective
  have := resultant_eq_prod_roots_sub (f.map (algebraMap R L))
    (g.map (algebraMap R L)) (hfm.map _) (hgm.map _) (hf.map _) (SplittingField.splits _)
  simp_rw [natDegree_map] at this
  rw [← resultant_map_map, ← Nat.add_sub_cancel' hg, resultant_add_right_deg _ _ _ _ _ (by simp),
    this, coeff_map, coeff_natDegree, hfm.leadingCoeff, map_one, one_pow, one_mul,
    map_sub_sprod_roots_eq_prod_map_eval _ _ (hgm.map _) (SplittingField.splits _),
    hf.roots_map, map_multiset_prod, Multiset.map_map]
  simp only [eval_map_algebraMap, Function.comp_apply, Multiset.map_map, L]
  congr; ext; simp [aeval_algebraMap_apply]

set_option linter.unusedVariables false in
-- the variable names are used in the code action of `induction`.
/-- An induction principle useful to prove statements about resultants.
Let `P` be a predicate on a polynomial.
If `R → S` injective implies `(∀ p : S[X], P p) → (∀ p : R[X], P p)`,
and if `R → S` surjective implies `(∀ p : R[X], P p) → (∀ p : S[X], P p)`,
then we may reduce to the case where `R` is a field and `p` splits. -/
nonrec lemma induction_of_Splits_of_injective_of_surjective.{u}
    {R : Type u} [CommRing R] (p : R[X])
    (P : ∀ {R : Type u} [CommRing R], R[X] → Prop)
    (Splits : ∀ (R : Type u) [Field R] (p : R[X]) (hp : p.Splits), P p)
    (injective : ∀ (R S : Type u) [CommRing R] [CommRing S]
      (φ : R →+* S) (hφ : Function.Injective φ) (p : R[X]) (IH : P (p.map φ)), P p)
    (surjective : ∀ (R S : Type u) [CommRing R] [CommRing S]
      (φ : R →+* S) (hφ : Function.Surjective φ) (p : S[X]) (IH : ∀ q : R[X], P q), P p) : P p := by
  wlog hR : IsDomain R generalizing R
  · exact surjective _ _ (MvPolynomial.eval₂Hom (algebraMap ℤ R) id)
      (fun x ↦ ⟨.X x, by simp [MvPolynomial.eval₂Hom]⟩) p
      (fun _ ↦ this _ inferInstance)
  wlog hR : IsField R generalizing R
  · exact injective _ _ _ (FaithfulSMul.algebraMap_injective R (FractionRing R)) _
      (this _ inferInstance (Field.toIsField _))
  wlog hp : p.Splits generalizing R
  · let inst := hR.toField
    exact injective _ _ _ (algebraMap R p.SplittingField).injective _
      (this _ inferInstance (Field.toIsField _) (SplittingField.splits _))
  let inst := hR.toField
  exact Splits _ _ hp

/-- `Res(f, g₁ * g₂) = Res(f, g₁) * Res(f, g₂)`. -/
nonrec lemma resultant_mul_right (f g₁ g₂ : R[X]) (m : ℕ) (hm : f.natDegree ≤ m) :
    resultant f (g₁ * g₂) m (g₁.natDegree + g₂.natDegree) =
      resultant f g₁ m * resultant f g₂ m := by
  wlog hgn : m = f.natDegree
  · obtain ⟨c, rfl⟩ := le_iff_exists_add.mp hm
    simp [resultant_add_left_deg, this f g₁ g₂, coeff_mul_degree_add_degree]
    ring_nf
  subst hgn; clear hm
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits R f hff =>
    simp [resultant_eq_prod_eval, natDegree_mul_le, hff]
    ring_nf
  | injective R SatisfiesM φ hφ f IH =>
    apply hφ
    have := IH (g₁.map φ) (g₂.map φ)
    rw [← Polynomial.map_mul] at this
    simpa only [resultant_map_map, ← map_mul, natDegree_map_eq_of_injective hφ] using this
  | surjective R S φ hφ f IH =>
    obtain ⟨f', hf', e⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ f)
    obtain ⟨g₁', hg₁, e₁⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ g₁)
    obtain ⟨g₂', hg₂, e₂⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ g₂)
    rw [← hg₁, ← hg₂, ← hf', ← Polynomial.map_mul]
    simp_rw [resultant_map_map, hg₁, hg₂, hf', ← natDegree_eq_natDegree e₁,
      ← natDegree_eq_natDegree e₂, ← natDegree_eq_natDegree e, IH, map_mul]

/-- `Res(f₁ * f₂, g) = Res(f₁, g) * Res(f₂, g)`. -/
/-
**Polynomial.resultant_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_mul_left (f₁ f₂ g : R[X]) (n : Nat) (hn : g.natDegree <= n) : re
sultant (f₁ * f₂) g (f₁.natDegree + f₂.natDegree) n = resultant f₁ g f₁.natDegre
e n * resultant f₂ g f₂.natDegree n
参数：f₁ f₂ g : R[X]；n : Nat；hn : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用定理 `Polynomial.resultant_mul_right`：∀ {R : Type u_1} [inst : CommRing R] (f 
g₁ g₂ : Polynomial R) (m : ℕ),   f.natDegree ≤ m → f.resultant (g₁ * g₂) m (g₁.n
atDegree + g₂.natDeg…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
`Res(f₁ * f₂, g) = Res(f₁, g) * Res(f₂, g)`.
-/
lemma resultant_mul_left (f₁ f₂ g : R[X]) (n : ℕ) (hn : g.natDegree ≤ n) :
    resultant (f₁ * f₂) g (f₁.natDegree + f₂.natDegree) n =
      resultant f₁ g f₁.natDegree n * resultant f₂ g f₂.natDegree n := by
  rw [resultant_comm, resultant_mul_right _ _ _ n hn, resultant_comm, resultant_comm f₂]
  ring_nf
  simp

/-- `Res(f, f) = 0` unless `deg f = 0`. Also see `resultant_self_eq_zero`. -/
@[simp] nonrec lemma resultant_self (f : R[X]) : resultant f f = 0 ^ f.natDegree := by
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits R f hf =>
    by_cases h : f.natDegree = 0
    · obtain ⟨r, rfl⟩ := natDegree_eq_zero.mp h; simp
    rw [resultant_eq_prod_eval _ _ _ le_rfl hf]
    simp [zero_pow h, h, hf.exists_eval_eq_zero (degree_ne_of_natDegree_ne h), eq_or_ne f]
  | injective R S φ hφ f IH =>
    apply hφ
    simpa only [resultant_map_map, natDegree_map_eq_of_injective hφ, map_zero, map_pow] using IH
  | surjective R S φ hφ f IH =>
    obtain ⟨f', hf', e⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ f)
    rw [← hf', resultant_map_map, hf', ← natDegree_eq_natDegree e, IH f', map_pow, map_zero]

/-
**Polynomial.resultant_self_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_self_eq_zero (f : R[X]) (h : f.natDegree != 0) : resultant f f =
 0
参数：f : R[X]；h : f.natDegree != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant_self`：∀ {R : Type u_1} [inst : CommRing R] (f : Pol
ynomial R), f.resultant f = 0 ^ f.natDegree
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resultant_self_eq_zero (f : R[X]) (h : f.natDegree ≠ 0) :
    resultant f f = 0 := by
  simp [resultant_self, h]
/-
**Polynomial.resultant_dvd_leadingCoeff_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：resultant_dvd_leadingCoeff_pow [IsDomain R] (f g : R[X]) (H : IsCoprime f 
g) : exists n, resultant f g ∣ f.leadingCoeff ^ n
参数：f g : R[X]；H : IsCoprime f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.resultant_zero_right_deg`：∀ {R : Type u_1} [inst : CommRing R
] (f g : Polynomial R) (m : ℕ), f.resultant g m 0 = g.coeff 0 ^ m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.isUnit_iff`：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ 
C r = p
· 使用定理 `IsUnit.of_mul_eq_one_right`：IsUnit.of_mul_eq_one_right [Monoid M] [IsDed
ekindFiniteMonoid M] {b : M} (a : M) (h : a * b = 1) : IsUnit b
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.resultant_mul_right`：∀ {R : Type u_1} [inst : CommRing R] (f 
g₁ g₂ : Polynomial R) (m : ℕ),   f.natDegree ≤ m → f.resultant (g₁ * g₂) m (g₁.n
atDegree + g₂.natDeg…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Polynomial.resultant_one_right`：∀ {R : Type u_1} [inst : CommRing R] (f 
: Polynomial R) (m n : ℕ), f.resultant 1 m n = f.coeff m ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
（共 35 条，此处仅展示前 30 条）
-/
lemma resultant_dvd_leadingCoeff_pow [IsDomain R] (f g : R[X]) (H : IsCoprime f g) :
    ∃ n, resultant f g ∣ f.leadingCoeff ^ n := by
  obtain rfl | hf := eq_or_ne f 0
  · simp only [isCoprime_zero_left, isUnit_iff] at H
    aesop
  obtain rfl | hg := eq_or_ne g 0
  · simp only [isCoprime_zero_right, isUnit_iff] at H
    aesop
  have ⟨a, b, e⟩ := H
  obtain rfl | ha := eq_or_ne a 0
  · obtain ⟨r, hr, rfl⟩ := isUnit_iff.mp (.of_mul_eq_one_right b (by simpa using e))
    simp [hr.pow]
  obtain rfl | hb := eq_or_ne b 0
  · obtain ⟨r, hr, rfl⟩ := isUnit_iff.mp (.of_mul_eq_one_right a (by simpa using e))
    simp [hr.pow]
  have := resultant_mul_right f b g _ le_rfl
  rw [← resultant_add_mul_right _ _ a _ _ _ le_rfl, add_comm, mul_comm f, e,
    resultant_one_right] at this
  · exact ⟨_, _, this.trans (mul_comm _ _)⟩
  · by_contra! H
    rw [← natDegree_mul ha hf, ← natDegree_mul hb hg] at H
    have := natDegree_add_eq_left_of_natDegree_lt H
    simp only [e, natDegree_one] at this
    lia
/-
**Polynomial.resultant_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_ne_zero [IsDomain R] (f g : R[X]) (H : IsCoprime f g) : resultan
t f g != 0
参数：f g : R[X]；H : IsCoprime f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Polynomial.resultant_dvd_leadingCoeff_pow`：resultant_dvd_leadingCoeff_po
w [IsDomain R] (f g : R[X]) (H : IsCoprime f g) : exists n, resultant f g ∣ f.le
adingCoeff ^ n
-/
lemma resultant_ne_zero [IsDomain R] (f g : R[X]) (H : IsCoprime f g) :
    resultant f g ≠ 0 := by
  obtain rfl | hf := eq_or_ne f 0
  · simp only [isCoprime_zero_left, isUnit_iff] at H
    aesop
  intro e
  simpa [e, hf] using resultant_dvd_leadingCoeff_pow f g H

@[simp]
/-
**Polynomial.resultant_prod_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_prod_left {ι : Type*} (s : Finset ι) (f : ι -> R[X]) (g : R[X]) 
(n : Nat) (hf : ∏ i in s, (f i).leadingCoeff != 0) (hn : g.natDegree <= n) : (∏ 
i in s, f i).resultant g (∏ i in s, f i).natDegree n = ∏ i in s, (f i).resultant
 g (f i).natDegree n
参数：s : Finset ι；f : ι -> R[X]；g : R[X]；n : Nat；hf : ∏ i in s, (f i).leadingCoeff
 != 0；hn : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Polynomial.leadingCoeff_prod'`：leadingCoeff_prod' (h : (∏ i in s, (f i).
leadingCoeff) != 0) : (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoef
f
· 使用引理 `Polynomial.resultant_mul_left`：resultant_mul_left (f₁ f₂ g : R[X]) (n : 
Nat) (hn : g.natDegree <= n) : resultant (f₁ * f₂) g (f₁.natDegree + f₂.natDegre
e) n = resultant f₁…
-/
lemma resultant_prod_left {ι : Type*} (s : Finset ι) (f : ι → R[X]) (g : R[X])
    (n : ℕ) (hf : ∏ i ∈ s, (f i).leadingCoeff ≠ 0) (hn : g.natDegree ≤ n) :
    (∏ i ∈ s, f i).resultant g (∏ i ∈ s, f i).natDegree n =
      ∏ i ∈ s, (f i).resultant g (f i).natDegree n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has IH =>
    have hf' : ∏ i ∈ s, (f i).leadingCoeff ≠ 0 := by aesop
    rw [Finset.prod_insert has, natDegree_mul' (by simpa [*, leadingCoeff_prod'] using hf),
      resultant_mul_left _ _ _ _ hn, IH hf', Finset.prod_insert has]

@[simp]
/-
**Polynomial.resultant_prod_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_prod_right {ι : Type*} (s : Finset ι) (f : R[X]) (g : ι -> R[X])
 (m : Nat) (hm : f.natDegree <= m) (hg : ∏ i in s, (g i).leadingCoeff != 0) : f.
resultant (∏ i in s, g i) m = ∏ i in s, f.resultant (g i) m
参数：s : Finset ι；f : R[X]；g : ι -> R[X]；m : Nat；hm : f.natDegree <= m；hg : ∏ i in
 s, (g i).leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Polynomial.resultant_prod_left`：resultant_prod_left {ι : Type*} (s : Fin
set ι) (f : ι -> R[X]) (g : R[X]) (n : Nat) (hf : ∏ i in s, (f i).leadingCoeff !
= 0) (hn : g.natDegr…
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Polynomial.natDegree_prod'`：natDegree_prod' (h : (∏ i in s, (f i).leadin
gCoeff) != 0) : (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree
-/
lemma resultant_prod_right {ι : Type*} (s : Finset ι) (f : R[X]) (g : ι → R[X])
    (m : ℕ) (hm : f.natDegree ≤ m) (hg : ∏ i ∈ s, (g i).leadingCoeff ≠ 0) :
    f.resultant (∏ i ∈ s, g i) m = ∏ i ∈ s, f.resultant (g i) m := by
  simp_rw [resultant_comm f]
  rw [resultant_prod_left _ _ _ _ hg hm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finset.mul_sum, natDegree_prod' _ _ hg]

@[simp]
/-
**Polynomial.resultant_pow_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_pow_left (hf : f.leadingCoeff ^ m != 0) (hn : g.natDegree <= n) 
: (f ^ m).resultant g (f ^ m).natDegree n = (f.resultant g f.natDegree n) ^ m
参数：hf : f.leadingCoeff ^ m != 0；hn : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Polynomial.resultant_prod_left`：resultant_prod_left {ι : Type*} (s : Fin
set ι) (f : ι -> R[X]) (g : R[X]) (n : Nat) (hf : ∏ i in s, (f i).leadingCoeff !
= 0) (hn : g.natDegr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma resultant_pow_left (hf : f.leadingCoeff ^ m ≠ 0) (hn : g.natDegree ≤ n) :
    (f ^ m).resultant g (f ^ m).natDegree n = (f.resultant g f.natDegree n) ^ m := by
  convert! resultant_prod_left (Finset.range m) (fun _ ↦ f) g n (by simpa) hn <;> simp

@[simp]
/-
**Polynomial.resultant_pow_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_pow_right (hm : f.natDegree <= m) (hg : g.leadingCoeff ^ n != 0)
 : f.resultant (g ^ n) m (g ^ n).natDegree = (f.resultant g m g.natDegree) ^ n
参数：hm : f.natDegree <= m；hg : g.leadingCoeff ^ n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Polynomial.resultant_prod_right`：resultant_prod_right {ι : Type*} (s : F
inset ι) (f : R[X]) (g : ι -> R[X]) (m : Nat) (hm : f.natDegree <= m) (hg : ∏ i 
in s, (g i).leadingCo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma resultant_pow_right (hm : f.natDegree ≤ m) (hg : g.leadingCoeff ^ n ≠ 0) :
    f.resultant (g ^ n) m (g ^ n).natDegree = (f.resultant g m g.natDegree) ^ n := by
  convert! resultant_prod_right (Finset.range n) f (fun _ ↦ g) m hm (by simpa) <;> simp
/-
**Polynomial.resultant_X_sub_C_pow_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_X_sub_C_pow_left (r : R) (g : R[X]) (m n : Nat) (hn : g.natDegre
e <= n) : ((X - C r) ^ m).resultant g m n = eval r g ^ m
参数：r : R；g : R[X]；m n : Nat；hn : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_pow'`：natDegree_pow' {n : Nat} (h : leadingCoeff p 
^ n != 0) : natDegree (p ^ n) = n * natDegree p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.resultant_X_sub_C_left`：∀ {R : Type u_1} [inst : CommRing R] 
(g : Polynomial R) (n : ℕ) (r : R),   g.natDegree ≤ n → (Polynomial.X - Polynomi
al.C r).resultant g 1 n…
· 使用引理 `Polynomial.resultant_pow_left`：resultant_pow_left (hf : f.leadingCoeff ^
 m != 0) (hn : g.natDegree <= n) : (f ^ m).resultant g (f ^ m).natDegree n = (f.
resultant g f.natDe…
-/
lemma resultant_X_sub_C_pow_left (r : R) (g : R[X]) (m n : ℕ) (hn : g.natDegree ≤ n) :
    ((X - C r) ^ m).resultant g m n = eval r g ^ m := by
  nontriviality R
  convert! resultant_pow_left _ _ _ _ _ _ <;> simp [natDegree_pow', hn]
/-
**Polynomial.resultant_X_sub_C_pow_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_X_sub_C_pow_right (f : R[X]) (r : R) (m n : Nat) (hm : f.natDegr
ee <= m) : f.resultant ((X - C r) ^ n) m n = (-1) ^ (m * n) * eval r f ^ n
参数：f : R[X]；r : R；m n : Nat；hm : f.natDegree <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用引理 `Polynomial.resultant_X_sub_C_pow_left`：resultant_X_sub_C_pow_left (r : R
) (g : R[X]) (m n : Nat) (hn : g.natDegree <= n) : ((X - C r) ^ m).resultant g m
 n = eval r g ^ m
-/
lemma resultant_X_sub_C_pow_right (f : R[X]) (r : R) (m n : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant ((X - C r) ^ n) m n = (-1) ^ (m * n) * eval r f ^ n := by
  rw [resultant_comm, resultant_X_sub_C_pow_left _ _ _ _ hm]
/-
**Polynomial.resultant_X_pow_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_X_pow_left (g : R[X]) (m n : Nat) (hn : g.natDegree <= n) : (X ^
 m).resultant g m n = g.coeff 0 ^ m
参数：g : R[X]；m n : Nat；hn : g.natDegree <= n。
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用引理 `Polynomial.resultant_X_sub_C_pow_left`：resultant_X_sub_C_pow_left (r : R
) (g : R[X]) (m n : Nat) (hn : g.natDegree <= n) : ((X - C r) ^ m).resultant g m
 n = eval r g ^ m
-/
lemma resultant_X_pow_left (g : R[X]) (m n : ℕ) (hn : g.natDegree ≤ n) :
    (X ^ m).resultant g m n = g.coeff 0 ^ m := by
  convert! resultant_X_sub_C_pow_left 0 g m n hn <;> simp [coeff_zero_eq_eval_zero]
/-
**Polynomial.resultant_X_pow_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_X_pow_right (f : R[X]) (m n : Nat) (hm : f.natDegree <= m) : f.r
esultant (X ^ n) m n = (-1) ^ (m * n) * f.coeff 0 ^ n
参数：f : R[X]；m n : Nat；hm : f.natDegree <= m。
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用引理 `Polynomial.resultant_X_sub_C_pow_right`：resultant_X_sub_C_pow_right (f :
 R[X]) (r : R) (m n : Nat) (hm : f.natDegree <= m) : f.resultant ((X - C r) ^ n)
 m n = (-1) ^ (m * n) * eval…
-/
lemma resultant_X_pow_right (f : R[X]) (m n : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (X ^ n) m n = (-1) ^ (m * n) * f.coeff 0 ^ n := by
  convert! resultant_X_sub_C_pow_right f 0 m n hm <;> simp [coeff_zero_eq_eval_zero]

nonrec lemma resultant_scaleRoots (f g : R[X]) (r : R) :
    resultant (f.scaleRoots r) (g.scaleRoots r) =
      r ^ (f.natDegree * g.natDegree) * resultant f g := by
  rw [natDegree_scaleRoots, natDegree_scaleRoots]
  obtain rfl | hf := eq_or_ne f 0; · simp
  obtain rfl | hg := eq_or_ne g 0; · simp
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits R f hf' =>
    by_cases hf0 : f.natDegree = 0
    · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hf0; simp
    by_cases hg0 : g.natDegree = 0
    · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hg0; simp
    obtain rfl | hr := eq_or_ne r 0
    · rw [scaleRoots_zero, scaleRoots_zero, Algebra.smul_def, Algebra.smul_def]
      simp [resultant_C_mul_right, resultant_X_pow_right, *, (Ne.symm hf0)]
    conv_lhs => rw [← natDegree_scaleRoots f r, ← natDegree_scaleRoots g r]
    rw [resultant_eq_prod_eval _ _ _ le_rfl hf',
      resultant_eq_prod_eval _ _ _ le_rfl (hf'.scaleRoots _),
      roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hr)]
    simp only [Multiset.map_map, Function.comp_def, scaleRoots_eval_mul]
    simp only [leadingCoeff_scaleRoots, natDegree_scaleRoots, Multiset.prod_map_mul,
      Multiset.map_const', Multiset.prod_replicate, ← hf'.natDegree_eq_card_roots]
    ring
  | injective R S φ hφ f IH =>
    have := IH (g.map φ) (φ r) (by simpa using (map_injective _ hφ).ne hf)
      (by simpa using (map_injective _ hφ).ne hg)
    apply hφ
    rw [← map_scaleRoots, ← map_scaleRoots] at this
    · simpa [natDegree_map_eq_of_injective hφ] using this
    all_goals simpa [map_eq_zero_iff _ hφ]
  | surjective R S φ hφ f IH =>
    obtain ⟨f', hf', ef⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ f)
    obtain ⟨g', hg', eg⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ g)
    obtain ⟨r, rfl⟩ := hφ r
    have hfl : f.leadingCoeff = φ f'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree ef, ← hf', coeff_map]
    have hgl : g.leadingCoeff = φ g'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree eg, ← hg', coeff_map]
    rw [← hf', ← map_scaleRoots _ _ _ (by simpa [← hfl]), ← hg',
      ← map_scaleRoots _ _ _ (by simpa [← hgl]), hf', hg',
      ← natDegree_eq_natDegree ef, ← natDegree_eq_natDegree eg,
      resultant_map_map, IH f' g' r (by aesop) (by aesop)]
    rw [← hf', ← hg', resultant_map_map]
    simp
/-
**Polynomial.resultant_integralNormalization** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：resultant_integralNormalization (f g : R[X]) (hg : g.natDegree != 0) : res
ultant (f.scaleRoots g.leadingCoeff) g.integralNormalization = g.leadingCoeff ^ 
(f.natDegree * (g.natDegree - 1)) * resultant f g
参数：f g : R[X]；hg : g.natDegree != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_scaleRoots`：natDegree_scaleRoots (p : R[X]) (s : R)
 : natDegree (scaleRoots p s) = natDegree p
· 使用引理 `Polynomial.natDegree_integralNormalization`：natDegree_integralNormalizat
ion : p.integralNormalization.natDegree = p.natDegree
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.resultant_zero_right_deg`：∀ {R : Type u_1} [inst : CommRing R
] (f g : Polynomial R) (m : ℕ), f.resultant g m 0 = g.coeff 0 ^ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.integralNormalization_zero`：integralNormalization_zero : inte
gralNormalization (0 : R[X]) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.resultant_scaleRoots`：∀ {R : Type u_1} [inst : CommRing R] (f
 g : Polynomial R) (r : R),   (f.scaleRoots r).resultant (g.scaleRoots r) = r ^ 
(f.natDegree * g.natD…
· 使用引理 `Polynomial.resultant_C_mul_right`：resultant_C_mul_right (r : R) : result
ant f (C r * g) m n = r ^ m * resultant f g m n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.integralNormalization_mul_C_leadingCoeff`：integralNormalizati
on_mul_C_leadingCoeff (p : R[X]) : integralNormalization p * C p.leadingCoeff = 
scaleRoots p p.leadingCoeff
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 60 条，此处仅展示前 30 条）
-/
lemma resultant_integralNormalization (f g : R[X]) (hg : g.natDegree ≠ 0) :
    resultant (f.scaleRoots g.leadingCoeff) g.integralNormalization =
      g.leadingCoeff ^ (f.natDegree * (g.natDegree - 1)) * resultant f g := by
  rw [natDegree_scaleRoots, natDegree_integralNormalization]
  wlog hR : IsDomain R
  · by_cases hf0 : f = 0; · simp [hf0]
    by_cases hg0 : g = 0; · simp [hg0]
    let S := MvPolynomial R ℤ
    let φ : S →+* R := MvPolynomial.eval₂Hom (algebraMap _ _) id
    have hφ : Function.Surjective φ := fun x ↦ ⟨.X x, by simp [φ, MvPolynomial.eval₂Hom]⟩
    obtain ⟨f', hf', ef⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ f)
    obtain ⟨g', hg', eg⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ g)
    have hfl : f.leadingCoeff = φ f'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree ef, ← hf', coeff_map]
    have hgl : g.leadingCoeff = φ g'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree eg, ← hg', coeff_map]
    rw [← natDegree_eq_natDegree ef, ← natDegree_eq_natDegree eg,
      ← hf', hgl, ← map_scaleRoots _ _ _ (by simpa [← hfl]), ← hg', integralNormalization_map _ _
      (by simpa [← hgl]), resultant_map_map,
      this f' g' (by simpa [natDegree_eq_natDegree eg]) inferInstance]
    simp [resultant_map_map]
  by_cases hg0 : g = 0; · simp [hg0]
  apply mul_right_injective₀ (a := g.leadingCoeff ^ f.natDegree) (by simp [hg0])
  dsimp
  have := resultant_scaleRoots f g g.leadingCoeff
  rw [natDegree_scaleRoots, natDegree_scaleRoots,
    ← integralNormalization_mul_C_leadingCoeff, mul_comm, resultant_C_mul_right] at this
  rw [this, ← mul_assoc, ← pow_add, add_comm, ← Nat.mul_add_one, Nat.sub_add_cancel (by lia)]

/-- `Res(f(x + r), g(x + r)) = Res(f, g)`. -/
nonrec lemma resultant_taylor (f g : R[X]) (r : R) :
    resultant (f.taylor r) (g.taylor r) = resultant f g := by
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits R f hf' =>
    induction hf' using Submonoid.closure_induction with
    | mem x h =>
      obtain (⟨s, rfl⟩ | ⟨s, rfl⟩) := h
      · rw [taylor_C]; simp
      · nontriviality R
        rw [map_add, taylor_X, taylor_C, add_assoc, ← map_add]
        simp [-map_add, taylor_eval]
    | one => simp
    | mul x y hx hy hx' hy' =>
      by_cases hx0 : x = 0; · simp [hx0]
      by_cases hy0 : y = 0; · simp [hy0]
      rw [taylor_mul, natDegree_mul' (by simp [*]), resultant_mul_left _ _ _ _ le_rfl]
      simp [natDegree_mul', hx0, hy0, resultant_mul_left, ← hx', ← hy']
  | injective R S φ hφ f IH =>
    apply hφ
    have := IH (g.map φ) (φ r)
    rw [← map_taylor, ← map_taylor] at this
    simpa [natDegree_map_eq_of_injective hφ] using this
  | surjective R S φ hφ f IH =>
    obtain ⟨f', hf', ef⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ f)
    obtain ⟨g', hg', eg⟩ := exists_degree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ g)
    obtain ⟨r, rfl⟩ := hφ r
    have hfl : f.leadingCoeff = φ f'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree ef, ← hf', coeff_map]
    have hgl : g.leadingCoeff = φ g'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree eg, ← hg', coeff_map]
    rw [natDegree_taylor, natDegree_taylor, ← hf', ← map_taylor, ← hg', ← map_taylor,
      resultant_map_map, resultant_map_map, hf', hg', ← natDegree_eq_natDegree ef,
      ← natDegree_eq_natDegree eg, ← IH f' g' r, natDegree_taylor, natDegree_taylor]

end resultant

section sylvesterMap

variable {m n} {R : Type*} [CommRing R]

attribute [local simp] Polynomial.mem_degreeLT

/-- The map `(p, q) ↦ f * q + g * p` whose associated matrix is `Syl(f, g)`. -/
@[simps]
noncomputable
/-
**Polynomial.sylvesterMap** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：sylvesterMap (f g : R[X]) (hf : f.natDegree <= m) (hg : g.natDegree <= n) 
: R[X]_m × R[X]_n ->ₗ[R] R[X]_(m + n) where toFun pq
参数：f g : R[X]；hf : f.natDegree <= m；hg : g.natDegree <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def sylvesterMap (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    R[X]_m × R[X]_n →ₗ[R] R[X]_(m + n) where
  toFun pq := ⟨f * pq.2 + g * pq.1, by
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
    rw [Polynomial.mem_degreeLT]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · by_cases hf' : f = 0; · simp_all
      exact (degree_mul_le _ _).trans_lt (WithBot.add_lt_add_of_le_of_lt (by simpa)
        (degree_le_of_natDegree_le hf) (by simpa using hq))
    · by_cases hg' : g = 0; · simp_all
      exact (degree_mul_le _ _).trans_lt ((WithBot.add_lt_add_of_le_of_lt (by simpa)
        (degree_le_of_natDegree_le hg) (by simpa using hp)).trans_eq (add_comm _ _))⟩
  map_add' _ _ := by ext1; dsimp; ring
  map_smul' _ _ := by ext1; simp
/-
**Polynomial.toMatrix_sylvesterMap** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：toMatrix_sylvesterMap (f g : R[X]) (hf : f.natDegree <= m) (hg : g.natDegr
ee <= n) : (sylvesterMap f g hf hg).toMatrix ((degreeLT.basis _ _).prod (degreeL
T.basis _ _)) (degreeLT.basis _ _) = (sylvester f g m n).reindex (.refl _) finSu
mFinEquiv.symm
参数：f g : R[X]；hf : f.natDegree <= m；hg : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用定理 `Polynomial.sylvesterMap_apply_coe`：∀ {m n : ℕ} {R : Type u_1} [inst : Co
mmRing R] (f g : Polynomial R) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)   (
pq : ↥(Polynomial.degre…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.degreeLT.basis_val`：∀ {R : Type u_1} [inst : Semiring R] {n :
 ℕ} (i : Fin n), ↑((Polynomial.degreeLT.basis R n) i) = Polynomial.X ^ ↑i
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.coeff_mul_X_pow'`：coeff_mul_X_pow' (p : R[X]) (n d : Nat) : (
p * X ^ n).coeff d = ite (n <= d) (p.coeff (d - n)) 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
-/
lemma toMatrix_sylvesterMap (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (sylvesterMap f g hf hg).toMatrix
      ((degreeLT.basis _ _).prod (degreeLT.basis _ _)) (degreeLT.basis _ _) =
    (sylvester f g m n).reindex (.refl _) finSumFinEquiv.symm := by
  ext i (j | j)
  · suffices (if j.1 ≤ i then g.coeff (i - j) else 0) =
      if j ≤ i.1 ∧ ↑i ≤ j + n then g.coeff (i - j) else 0 by
        simpa [LinearMap.toMatrix_apply, sylvester, coeff_mul_X_pow']
    rw [ite_and]
    split_ifs with h₁ h₂ <;> try rfl
    exact coeff_eq_zero_of_natDegree_lt (by lia)
  · suffices (if j.1 ≤ i then f.coeff (i - j) else 0) =
      if j ≤ i.1 ∧ ↑i ≤ j + m then f.coeff (i - j) else 0 by
        simpa [LinearMap.toMatrix_apply, sylvester, coeff_mul_X_pow']
    rw [ite_and]
    split_ifs with h₁ h₂ <;> try rfl
    exact coeff_eq_zero_of_natDegree_lt (by lia)
/-
**Polynomial.toMatrix_sylvesterMap'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：toMatrix_sylvesterMap' (f g : R[X]) (hf : f.natDegree <= m) (hg : g.natDeg
ree <= n) : (sylvesterMap f g hf hg).toMatrix (((degreeLT.basis _ _).prod (degre
eLT.basis _ _)).reindex finSumFinEquiv) (degreeLT.basis _ _) = sylvester f g m n
参数：f g : R[X]；hf : f.natDegree <= m；hg : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用定理 `Polynomial.sylvesterMap_apply_coe`：∀ {m n : ℕ} {R : Type u_1} [inst : Co
mmRing R] (f g : Polynomial R) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)   (
pq : ↥(Polynomial.degre…
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用引理 `Polynomial.toMatrix_sylvesterMap`：toMatrix_sylvesterMap (f g : R[X]) (hf
 : f.natDegree <= m) (hg : g.natDegree <= n) : (sylvesterMap f g hf hg).toMatrix
 ((degreeLT.basis _ _)…
-/
lemma toMatrix_sylvesterMap' (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (sylvesterMap f g hf hg).toMatrix
      (((degreeLT.basis _ _).prod (degreeLT.basis _ _)).reindex finSumFinEquiv)
      (degreeLT.basis _ _) = sylvester f g m n := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simpa [LinearMap.toMatrix_apply] using congr($(toMatrix_sylvesterMap f g hf hg) i j)

/-- The adjugate map of the sylvester map. It takes `P` to `(p, q)` such that
`f * q + g * p = Res(f, g) * P`. -/
noncomputable
/-
**Polynomial.adjSylvester** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：adjSylvester (f g : R[X]) : R[X]_(m + n) ->ₗ[R] R[X]_m × R[X]_n
参数：f g : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def adjSylvester (f g : R[X]) :
    R[X]_(m + n) →ₗ[R] R[X]_m × R[X]_n :=
  (f.sylvester g m n).adjugate.toLin (degreeLT.basis R (m + n))
    (((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv)
/-
**Polynomial.sylveserMap_comp_adjSylvester** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
`。
形式化陈述：sylveserMap_comp_adjSylvester (f g : R[X]) (hf : f.natDegree <= m) (hg : g
.natDegree <= n) : sylvesterMap f g hf hg ∘ₗ adjSylvester f g = f.resultant g m 
n • LinearMap.id
参数：f g : R[X]；hf : f.natDegree <= m；hg : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.resultant.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (f g : P
olynomial R) (m n : ℕ), f.resultant g m n = (f.sylvester g m n).det
· 使用定理 `Matrix.toLin_one`：Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id
· 使用引理 `Polynomial.toMatrix_sylvesterMap'`：toMatrix_sylvesterMap' (f g : R[X]) (
hf : f.natDegree <= m) (hg : g.natDegree <= n) : (sylvesterMap f g hf hg).toMatr
ix (((degreeLT.basis _ …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Matrix.toLin_toMatrix`：Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) : Matrix
.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
-/
lemma sylveserMap_comp_adjSylvester (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    sylvesterMap f g hf hg ∘ₗ adjSylvester f g = f.resultant g m n • LinearMap.id := by
  let b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv
  let b₂ := degreeLT.basis R (m + n)
  have := congr(Matrix.toLin b₂ b₂ $(((sylvesterMap f g hf hg).toMatrix b₁ b₂).mul_adjugate))
  rwa [Matrix.toLin_mul b₂ b₁ b₂, Matrix.toLin_toMatrix, map_smul,
    toMatrix_sylvesterMap', Matrix.toLin_one, ← resultant] at this
/-
**Polynomial.adjSylvester_comp_sylveserMap** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
`。
形式化陈述：adjSylvester_comp_sylveserMap (f g : R[X]) (hf : f.natDegree <= m) (hg : g
.natDegree <= n) : adjSylvester f g ∘ₗ sylvesterMap f g hf hg = f.resultant g m 
n • LinearMap.id
参数：f g : R[X]；hf : f.natDegree <= m；hg : g.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate_mul`：adjugate_mul (A : Matrix n n α) : adjugate A * A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.resultant.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (f g : P
olynomial R) (m n : ℕ), f.resultant g m n = (f.sylvester g m n).det
· 使用定理 `Matrix.toLin_one`：Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id
· 使用引理 `Polynomial.toMatrix_sylvesterMap'`：toMatrix_sylvesterMap' (f g : R[X]) (
hf : f.natDegree <= m) (hg : g.natDegree <= n) : (sylvesterMap f g hf hg).toMatr
ix (((degreeLT.basis _ …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Matrix.toLin_toMatrix`：Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) : Matrix
.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
-/
lemma adjSylvester_comp_sylveserMap (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    adjSylvester f g ∘ₗ sylvesterMap f g hf hg = f.resultant g m n • LinearMap.id := by
  let b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv
  let b₂ := degreeLT.basis R (m + n)
  have := congr(Matrix.toLin b₁ b₁ $(((sylvesterMap f g hf hg).toMatrix b₁ b₂).adjugate_mul))
  rwa [Matrix.toLin_mul b₁ b₂ b₁, Matrix.toLin_toMatrix, map_smul,
    toMatrix_sylvesterMap', Matrix.toLin_one, ← resultant] at this

/-- Note that if `n = m = 0` then `resultant = 1` but `f` and `g` aren't necessarily coprime. -/
/-
**Polynomial.exists_mul_add_mul_eq_C_resultant** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial`。
形式化陈述：exists_mul_add_mul_eq_C_resultant (f g : R[X]) (hf : f.natDegree <= m) (hg
 : g.natDegree <= n) (H : m != 0 ∨ n != 0) : exists p q, p.degree < ↑n ∧ q.degre
e < ↑m ∧ f * p + g * q = C (f.resultant g m n)
参数：f g : R[X]；hf : f.natDegree <= m；hg : g.natDegree <= n；H : m != 0 ∨ n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.degree_of_subsingleton`：degree_of_subsingleton [Subsingleton 
R] : degree p = ⊥
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `WithBot.instIsOrderedRing`：∀ {α : Type u_1} [inst : DecidableEq α] [inst
_1 : CommSemiring α] [inst_2 : PartialOrder α] [IsOrderedRing α]   [inst_4 : Can
onicallyOrdered…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `Polynomial.sylveserMap_comp_adjSylvester`：sylveserMap_comp_adjSylvester 
(f g : R[X]) (hf : f.natDegree <= m) (hg : g.natDegree <= n) : sylvesterMap f g 
hf hg ∘ₗ adjSylvester f g = f.…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Polynomial.sylvesterMap_apply_coe`：∀ {m n : ℕ} {R : Type u_1} [inst : Co
mmRing R] (f g : Polynomial R) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)   (
pq : ↥(Polynomial.degre…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Mathlib.Tactic.TermCongr.cHole.congr_simp`：∀ {α : Sort u} (val val_1 : α
), val = val_1 → ∀ {p p_1 : Prop} (e_p : p = p_1) (_pf : p), val = val_1
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩

--- 原说明 ---
Note that if `n = m = 0` then `resultant = 1` but `f` and `g` aren't necessarily
 coprime.
-/
lemma exists_mul_add_mul_eq_C_resultant
    (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0) :
    ∃ p q, p.degree < ↑n ∧ q.degree < ↑m ∧ f * p + g * q = C (f.resultant g m n) := by
  nontriviality R
  let X := adjSylvester f g ⟨1, by simpa [Polynomial.mem_degreeLT,
    ← Nat.cast_add, Nat.pos_iff_ne_zero, not_and_or, -not_and] using H⟩
  have : ((sylvesterMap f g hf hg X)).1 = _ :=
    congr(($(sylveserMap_comp_adjSylvester f g hf hg) _).1)
  refine ⟨X.2, X.1, by simpa [-SetLike.coe_mem] using X.2.2,
    by simpa [-SetLike.coe_mem] using X.1.2, by simpa [Algebra.smul_def] using this⟩
/-
**Polynomial.isUnit_resultant_iff_isCoprime** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：isUnit_resultant_iff_isCoprime {f g : R[X]} (hf : f.Monic) : IsUnit (resul
tant f g) ↔ IsCoprime f g
参数：hf : f.Monic。
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
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_one_of_monic_natDegree_zero`：eq_one_of_monic_natDegree_zer
o (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1
· 使用引理 `Polynomial.exists_mul_add_mul_eq_C_resultant`：exists_mul_add_mul_eq_C_re
sultant (f g : R[X]) (hf : f.natDegree <= m) (hg : g.natDegree <= n) (H : m != 0
 ∨ n != 0) : exists p q, p.degree …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.resultant_mul_right`：∀ {R : Type u_1} [inst : CommRing R] (f 
g₁ g₂ : Polynomial R) (m : ℕ),   f.natDegree ≤ m → f.resultant (g₁ * g₂) m (g₁.n
atDegree + g₂.natDeg…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
（共 47 条，此处仅展示前 30 条）
-/
lemma isUnit_resultant_iff_isCoprime {f g : R[X]} (hf : f.Monic) :
    IsUnit (resultant f g) ↔ IsCoprime f g := by
  by_cases hf0 : f.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hf hf0; simp [isCoprime_one_left]
  refine ⟨fun H ↦ ?_, ?_⟩
  · obtain ⟨p, q, hp, hq, e⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (by simp [hf0])
    exact ⟨C (H.unit⁻¹).1 * p, C (H.unit⁻¹).1 * q, by simp only [mul_assoc, ← mul_add, mul_comm p,
      mul_comm q, e, ← map_mul, IsUnit.val_inv_mul, map_one]⟩
  · intro ⟨a, b, e⟩
    suffices 1 = f.resultant b * f.resultant g from isUnit_iff_exists_inv'.mpr ⟨_, this.symm⟩
    have := resultant_mul_right f b g _ le_rfl
    obtain rfl | hb0 := eq_or_ne a 0
    · rw [show b * g = 1 by simpa using e, resultant_one_right] at this
      simpa [hf.leadingCoeff] using this
    · rw [← resultant_add_mul_right _ _ a _ _ _ le_rfl, add_comm, mul_comm, e, ← C.map_one] at this
      · simpa [hf.leadingCoeff] using this
      · by_contra! H
        replace H := natDegree_mul_le.trans_lt H
        rw [add_comm, ← hf.natDegree_mul' hb0, mul_comm f] at H
        have := natDegree_add_eq_left_of_natDegree_lt H
        simp only [e, natDegree_one] at this
        lia
/-
**Polynomial.resultant_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_eq_zero_iff {K : Type*} [Field K] {f g : K[X]} : resultant f g =
 0 ↔ (f != 0 ∨ g != 0) ∧ ¬ IsCoprime f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.resultant_zero_right_deg`：∀ {R : Type u_1} [inst : CommRing R
] (f g : Polynomial R) (m : ℕ), f.resultant g m 0 = g.coeff 0 ^ m
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.resultant_zero_left_deg`：∀ {R : Type u_1} [inst : CommRing R]
 (f g : Polynomial R) (m : ℕ), f.resultant g 0 m = f.coeff 0 ^ m
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
（共 43 条，此处仅展示前 30 条）
-/
lemma resultant_eq_zero_iff {K : Type*} [Field K] {f g : K[X]} :
    resultant f g = 0 ↔ (f ≠ 0 ∨ g ≠ 0) ∧ ¬ IsCoprime f g := by
  obtain rfl | hf := eq_or_ne f 0
  · obtain rfl | hg := eq_or_ne g 0; · simp
    simpa [isCoprime_zero_left, isUnit_iff, hg, natDegree_eq_zero] using
      show (∀ x, C x ≠ g) ↔ ∀ x ≠ 0, C x ≠ g by aesop
  have H : (C f.leadingCoeff⁻¹ * f).Monic := by
    rw [Monic, ← coeff_natDegree, natDegree_C_mul (by simpa), coeff_C_mul]; simp [hf]
  have := isUnit_resultant_iff_isCoprime (f := C f.leadingCoeff⁻¹ * f) (g := g) H
  rw [resultant_C_mul_left, IsUnit.mul_iff, natDegree_C_mul (by simp [hf]),
    isCoprime_mul_unit_left_left (isUnit_C.mpr (by simp [hf]))] at this
  simp [← this, hf]

end sylvesterMap

section disc

variable {R : Type*} [CommRing R]

/-- The discriminant of a polynomial, defined as the determinant of `f.sylvesterDeriv` modified
by a sign. The sign is chosen so polynomials over `ℝ` with all roots real have non-negative
discriminant. -/
/-
**Polynomial.discr** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：discr (f : R[X]) : R
参数：f : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discriminant of a polynomial, defined as the determinant of `f.sylvesterDeri
v` modified
by a sign. The sign is chosen so polynomials over `ℝ` with all roots real have n
on-negative
discriminant.
-/
noncomputable def discr (f : R[X]) : R :=
  f.sylvesterDeriv.det * (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)

set_option backward.isDefEq.respectTransparency.types false in
/-- The discriminant of a constant polynomial is `1`. -/
/-
**Polynomial.discr_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (r : R), (Polynomial.C r).discr = 1
参数：r : R；Polynomial.C r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.submatrix_empty`：submatrix_empty (A : Matrix m' n' α) (row : Fin 
0 -> m') (col : o' -> n') : submatrix A row col = of ![]
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.det_fin_zero`：det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A
 = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The discriminant of a constant polynomial is `1`.
-/
@[simp] lemma discr_C (r : R) : discr (C r) = 1 := by
  let e : Fin ((C r).natDegree - 1 + (C r).natDegree) ≃ Fin 0 := finCongr (by simp)
  simp [discr, ← Matrix.det_reindex_self e]

/-- The discriminant of a linear polynomial is `1`. -/
/-
**Polynomial.discr_of_degree_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：discr_of_degree_eq_one {f : R[X]} (hf : f.degree = 1) : discr f = 1
参数：hf : f.degree = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq_of_pos`：degree_eq_iff_natDegree_eq
_of_pos {p : R[X]} {n : Nat} (hn : 0 < n) : p.degree = n ↔ p.natDegree = n
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The discriminant of a linear polynomial is `1`.
-/
lemma discr_of_degree_eq_one {f : R[X]} (hf : f.degree = 1) : discr f = 1 := by
  rw [← Nat.cast_one, degree_eq_iff_natDegree_eq_of_pos one_pos] at hf
  let e : Fin (f.natDegree - 1 + f.natDegree) ≃ Fin 1 := finCongr (by lia)
  have : f.sylvesterDeriv.reindex e e = !![1] := by
    have : NeZero (f.natDegree - 1 + f.natDegree) := ⟨by lia⟩
    ext ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨rfl⟩ : i = 0 := by lia
    obtain ⟨rfl⟩ : j = 0 := by lia
    simp [e, sylvesterDeriv, mul_comm, hf]
  simp [discr, ← Matrix.det_reindex_self e, this, hf]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Standard formula for the discriminant of a quadratic polynomial. -/
/-
**Polynomial.discr_of_degree_eq_two** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：discr_of_degree_eq_two {f : R[X]} (hf : f.degree = 2) : discr f = f.coeff 
1 ^ 2 - 4 * f.coeff 0 * f.coeff 2
参数：hf : f.degree = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq_of_pos`：degree_eq_iff_natDegree_eq
_of_pos {p : R[X]} {n : Nat} (hn : 0 < n) : p.degree = n ↔ p.natDegree = n
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Polynomial.discr.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (f : Polynom
ial R),   f.discr = f.sylvesterDeriv.det * (-1) ^ (f.natDegree * (f.natDegree - 
1) / 2)
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
（共 116 条，此处仅展示前 30 条）

--- 原说明 ---
Standard formula for the discriminant of a quadratic polynomial.
-/
lemma discr_of_degree_eq_two {f : R[X]} (hf : f.degree = 2) :
    discr f = f.coeff 1 ^ 2 - 4 * f.coeff 0 * f.coeff 2 := by
  rw [← Nat.cast_two, degree_eq_iff_natDegree_eq_of_pos two_pos] at hf
  let e : Fin (f.natDegree - 1 + f.natDegree) ≃ Fin 3 := finCongr (by lia)
  rw [discr, ← Matrix.det_reindex_self e]
  have : f.sylvesterDeriv.reindex e e =
    !![f.coeff 0,     f.coeff 1,         0;
        f.coeff 1, 2 * f.coeff 2, f.coeff 1;
        1,                     0,         2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, sylvesterDeriv, sylvester, coeff_derivative, mul_comm, Fin.addCases,
        one_add_one_eq_two, hf, Fin.cast]
  simp only [this, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val, hf]
  ring_nf

/-- Relation between the resultant and the discriminant.

(Note this is actually false when `f` is a constant polynomial not equal to 1, so the assumption on
the degree is genuinely needed.) -/
/-
**Polynomial.resultant_deriv** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：resultant_deriv {f : R[X]} (hf : 0 < f.degree) : resultant f f.derivative 
f.natDegree (f.natDegree - 1) = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f
.leadingCoeff * f.discr
参数：hf : 0 < f.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.resultant_comm`：resultant_comm : resultant f g m n = (-1) ^ (
m * n) * resultant g f n m
· 使用定理 `Polynomial.resultant.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (f g : P
olynomial R) (m n : ℕ), f.resultant g m n = (f.sylvester g m n).det
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用引理 `Polynomial.sylvesterDeriv_updateRow`：sylvesterDeriv_updateRow (f : R[X])
 (hf : 0 < f.natDegree) : (sylvesterDeriv f).updateRow ⟨2 * f.natDegree - 2, by 
lia⟩ (f.leadingCoeff • (s…
· 使用定理 `Matrix.det_updateRow_smul`：det_updateRow_smul (M : Matrix n n R) (j : n)
 (s : R) (u : n -> R) : det (updateRow M j <| s • u) = s * det (updateRow M j u)
· 使用定理 `Matrix.updateRow_eq_self`：updateRow_eq_self [DecidableEq m] (A : Matrix 
m n α) (i : m) : A.updateRow i (A i) = A
· 使用定理 `Polynomial.discr.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (f : Polynom
ial R),   f.discr = f.sylvesterDeriv.det * (-1) ^ (f.natDegree * (f.natDegree - 
1) / 2)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
Relation between the resultant and the discriminant.

(Note this is actually false when `f` is a constant polynomial not equal to 1, s
o the assumption on
the degree is genuinely needed.)
-/
lemma resultant_deriv {f : R[X]} (hf : 0 < f.degree) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.discr := by
  rw [← natDegree_pos_iff_degree_pos] at hf
  rw [resultant_comm, resultant, ← sylvesterDeriv_updateRow f hf, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self, discr, mul_comm f.natDegree]
  ring_nf
  rw [Nat.div_mul_cancel (by convert! Nat.two_dvd_mul_add_one (f.natDegree - 1) using 2; lia)]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**Polynomial.sylvesterDeriv_of_natDegree_eq_three** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sylvesterDeriv_of_natDegree_eq_three {f : R[X]} (hf : f.natDegree = 3) :
    f.sylvesterDeriv.reindex (finCongr <| by rw [hf]) (finCongr <| by rw [hf]) =
    !![ f.coeff 0,         0, 1 * f.coeff 1,             0,             0;
        f.coeff 1, f.coeff 0, 2 * f.coeff 2, 1 * f.coeff 1,             0;
        f.coeff 2, f.coeff 1, 3 * f.coeff 3, 2 * f.coeff 2, 1 * f.coeff 1;
        f.coeff 3, f.coeff 2,             0, 3 * f.coeff 3, 2 * f.coeff 2;
                0,         1,             0,             0,             3] := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  -- In this proof we do as much as possible of the `simp` work before drilling down into the
  -- `fin_cases` constructs. This means the simps are not terminal, so they are not squeezed;
  -- but the proof runs much faster this way.
  simp only [sylvesterDeriv, hf, OfNat.ofNat_ne_zero, ↓reduceDIte, sylvester, Fin.addCases,
    Nat.add_one_sub_one, Fin.val_castLT, mem_Icc, Fin.val_fin_le, Fin.val_subNat, Fin.val_cast,
    tsub_le_iff_right, coeff_derivative, eq_rec_constant, dite_eq_ite, Nat.reduceMul, Nat.reduceSub,
    Nat.cast_ofNat, Matrix.reindex_apply, finCongr_symm, Matrix.submatrix_apply, finCongr_apply,
    Fin.cast_mk, Matrix.updateRow_apply, Fin.mk.injEq, Matrix.of_apply, Fin.mk_le_mk, one_mul,
    Matrix.cons_val', Matrix.cons_val_fin_one]
  have hi' : i ∈ Finset.range 5 := Finset.mem_range.mpr hi
  have hj' : j ∈ Finset.range 5 := Finset.mem_range.mpr hj
  fin_cases hi' <;>
  · simp only [and_true, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      le_add_iff_nonneg_left, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
      Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLeDiff, nonpos_iff_eq_zero,
      OfNat.one_ne_ofNat, ↓reduceIte, zero_add, zero_le]
    fin_cases hj' <;> simp [mul_comm, one_add_one_eq_two, (by norm_num : (2 : R) + 1 = 3)]

/-- Standard formula for the discriminant of a cubic polynomial. -/
/-
**Polynomial.discr_of_degree_eq_three** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：discr_of_degree_eq_three {f : R[X]} (hf : f.degree = 3) : discr f = f.coef
f 2 ^ 2 * f.coeff 1 ^ 2 - 4 * f.coeff 3 * f.coeff 1 ^ 3 - 4 * f.coeff 2 ^ 3 * f.
coeff 0 - 27 * f.coeff 3 ^ 2 * f.coeff 0 ^ 2 + 18 * f.coeff 3 * f.coeff 2 * f.co
eff 1 * f.coeff 0
参数：hf : f.degree = 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.discr.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (f : Polynom
ial R),   f.discr = f.sylvesterDeriv.det * (-1) ^ (f.natDegree * (f.natDegree - 
1) / 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.Resultant.Basic.0.Polynomial.sylv
esterDeriv_of_natDegree_eq_three`：∀ {R : Type u_1} [inst : CommRing R] {f : Poly
nomial R} (hf : f.natDegree = 3),   (Matrix.reindex (finCongr ⋯) (finCongr ⋯)) f
.sylvesterDeri…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.det_succ_row_zero`：det_succ_row_zero {n : Nat} (A : Matrix (Fin n
.succ) (Fin n.succ) R) : det A = ∑ j : Fin n.succ, (-1) ^ (j : Nat) * A 0 j * de
t (A.submatrix…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `Matrix.det_fin_three`：det_fin_three (A : Matrix (Fin 3) (Fin 3) R) : det
 A = A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 + A 0
 1 * A 1 2…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_fin_eq_sum_range`：∀ {β : Type u_2} [inst : AddCommMonoid β] {
n : ℕ} (c : Fin n → β),   ∑ i, c i = ∑ i ∈ Finset.range n, if h : i < n then c ⟨
i, h⟩ else 0
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
Standard formula for the discriminant of a cubic polynomial.
-/
lemma discr_of_degree_eq_three {f : R[X]} (hf : f.degree = 3) :
    discr f = f.coeff 2 ^ 2 * f.coeff 1 ^ 2
              - 4 * f.coeff 3 * f.coeff 1 ^ 3
              - 4 * f.coeff 2 ^ 3 * f.coeff 0
              - 27 * f.coeff 3 ^ 2 * f.coeff 0 ^ 2
              + 18 * f.coeff 3 * f.coeff 2 * f.coeff 1 * f.coeff 0 := by
  apply natDegree_eq_of_degree_eq_some at hf
  let e : Fin ((f.natDegree - 1) + f.natDegree) ≃ Fin 5 := finCongr (by rw [hf])
  rw [discr, ← Matrix.det_reindex_self e, sylvesterDeriv_of_natDegree_eq_three hf]
  simp [Matrix.det_succ_row_zero (n := 4), Matrix.det_succ_row_zero (n := 3), Fin.succAbove,
    Matrix.det_fin_three, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hf]
  ring_nf

end disc

end Polynomial

