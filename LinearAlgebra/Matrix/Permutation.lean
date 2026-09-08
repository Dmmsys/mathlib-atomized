/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Permutation matrices

This file defines the matrix associated with a permutation

## Main definitions

- `Equiv.Perm.permMatrix`: the permutation matrix associated with an `Equiv.Perm`

## Main results

- `Matrix.det_permutation`: the determinant is the sign of the permutation
- `Matrix.trace_permutation`: the trace is the number of fixed points of the permutation

-/

@[expose] public section

open Equiv

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable (R) in
/-- the permutation matrix associated with an `Equiv.Perm` -/
/-
**Equiv.Perm.permMatrix** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Equiv.Perm.permMatrix [Zero R] [One R] : Matrix n n R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the permutation matrix associated with an `Equiv.Perm`
-/
abbrev Equiv.Perm.permMatrix [Zero R] [One R] : Matrix n n R :=
  σ.toPEquiv.toMatrix

namespace Matrix

/-
**Matrix.permMatrix_refl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_2} [inst : DecidableEq n] [inst_1 : Zero R] [
inst_2 : One R],   Equiv.Perm.permMatrix R (Equiv.refl n) = 1
参数：Equiv.refl n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma permMatrix_refl [Zero R] [One R] : Equiv.Perm.permMatrix R (.refl n) = 1 := by
  simp [← Matrix.ext_iff, Matrix.one_apply]

@[simp]
/-
**Matrix.permMatrix_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：permMatrix_one [Zero R] [One R] : (1 : Equiv.Perm n).permMatrix R = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.permMatrix_refl`：∀ {n : Type u_1} {R : Type u_2} [inst : Decidabl
eEq n] [inst_1 : Zero R] [inst_2 : One R],   Equiv.Perm.permMatrix R (Equiv.refl
 n) = 1
-/
lemma permMatrix_one [Zero R] [One R] : (1 : Equiv.Perm n).permMatrix R = 1 :=
  permMatrix_refl

@[simp]
/-
**Matrix.transpose_permMatrix** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：transpose_permMatrix [Zero R] [One R] : (σ.permMatrix R).transpose = (σ⁻¹)
.permMatrix R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PEquiv.toMatrix_symm`：toMatrix_symm [DecidableEq m] [DecidableEq n] [Zer
o α] [One α] (f : m ≃. n) : (f.symm.toMatrix : Matrix n m α) = f.toMatrixᵀ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.toPEquiv_symm`：toPEquiv_symm (f : α ≃ β) : f.symm.toPEquiv = f.toP
Equiv.symm
· 使用定理 `Equiv.Perm.inv_def`：inv_def (f : Perm α) : f⁻¹ = f.symm
-/
lemma transpose_permMatrix [Zero R] [One R] : (σ.permMatrix R).transpose = (σ⁻¹).permMatrix R := by
  rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, ← Equiv.Perm.inv_def]

@[simp]
/-
**Matrix.conjTranspose_permMatrix** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_permMatrix [NonAssocSemiring R] [StarRing R] : (σ.permMatrix
 R).conjTranspose = (σ⁻¹).permMatrix R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Matrix.transpose_permMatrix`：transpose_permMatrix [Zero R] [One R] : (σ.
permMatrix R).transpose = (σ⁻¹).permMatrix R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
-/
lemma conjTranspose_permMatrix [NonAssocSemiring R] [StarRing R] :
    (σ.permMatrix R).conjTranspose = (σ⁻¹).permMatrix R := by
  simp only [conjTranspose, transpose_permMatrix, map]
  aesop

variable [Fintype n]

/-- The determinant of a permutation matrix equals its sign. -/
@[simp]
/-
**Matrix.det_permutation** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_permutation [CommRing R] : det (σ.permMatrix R) = Perm.sign σ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `PEquiv.toMatrix_toPEquiv_mul`：toMatrix_toPEquiv_mul [Fintype m] [Decidab
leEq m] [NonAssocSemiring α] (f : l ≃ m) (M : Matrix m n α) : f.toPEquiv.toMatri
x * M = M.submatri…
· 使用定理 `Matrix.det_permute`：det_permute (σ : Perm n) (M : Matrix n n R) : (M.sub
matrix σ id).det = Perm.sign σ * M.det
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The determinant of a permutation matrix equals its sign.
-/
theorem det_permutation [CommRing R] : det (σ.permMatrix R) = Perm.sign σ := by
  rw [← Matrix.mul_one (σ.permMatrix R), PEquiv.toMatrix_toPEquiv_mul,
    det_permute, det_one, mul_one]

/-- The trace of a permutation matrix equals the number of fixed points. -/
/-
**Matrix.trace_permutation** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_permutation [AddCommMonoidWithOne R] : trace (σ.permMatrix R) = (Fun
ction.fixedPoints σ).ncard
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
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trace of a permutation matrix equals the number of fixed points.
-/
theorem trace_permutation [AddCommMonoidWithOne R] :
    trace (σ.permMatrix R) = (Function.fixedPoints σ).ncard := by
  delta trace
  simp [toPEquiv_apply, ← Set.ncard_coe_finset, Function.fixedPoints, Function.IsFixedPt]
/-
**Matrix.permMatrix_mulVec** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：permMatrix_mulVec {v : n -> R} [CommRing R] : σ.permMatrix R *ᵥ v = v ∘ σ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_eq_sum`：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix
 m n α) : M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `PEquiv.transpose_toMatrix_toPEquiv_apply`：transpose_toMatrix_toPEquiv_ap
ply [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (j) : f.toPEqui
v.toMatrixᵀ j = Pi.single (f.s…
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
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
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma permMatrix_mulVec {v : n → R} [CommRing R] :
    σ.permMatrix R *ᵥ v = v ∘ σ := by
  ext j
  simp [mulVec_eq_sum, Pi.single, Function.update, Equiv.eq_symm_apply]
/-
**Matrix.vecMul_permMatrix** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：vecMul_permMatrix {v : n -> R} [CommRing R] : v ᵥ* σ.permMatrix R = v ∘ σ.
symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecMul_eq_sum`：vecMul_eq_sum [Fintype m] (v : m -> α) (M : Matrix
 m n α) : v ᵥ* M = ∑ i, v i • M i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `PEquiv.toMatrix_toPEquiv_apply`：toMatrix_toPEquiv_apply [DecidableEq n] 
[Zero α] [One α] (f : m ≃ n) (i) : f.toPEquiv.toMatrix i = Pi.single (f i) (1 : 
α)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
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
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vecMul_permMatrix {v : n → R} [CommRing R] :
    v ᵥ* σ.permMatrix R = v ∘ σ.symm := by
  ext j
  simp [vecMul_eq_sum, Pi.single, Function.update, ← Equiv.symm_apply_eq σ]

@[simp]
/-
**Matrix.permMatrix_mul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：permMatrix_mul [NonAssocSemiring R] : (σ * τ).permMatrix R = τ.permMatrix 
R * σ.permMatrix R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.permMatrix.eq_1`：∀ {n : Type u_1} (R : Type u_2) [inst : Deci
dableEq n] (σ : Equiv.Perm n) [inst_1 : Zero R] [inst_2 : One R],   Equiv.Perm.p
ermMatrix R σ = …
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.Perm.mul_def`：mul_def (f g : Perm α) : f * g = g.trans f
· 使用定理 `Equiv.toPEquiv_trans`：toPEquiv_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans 
g).toPEquiv = f.toPEquiv.trans g.toPEquiv
· 使用定理 `PEquiv.toMatrix_trans`：toMatrix_trans [Fintype m] [DecidableEq m] [Decid
ableEq n] [NonAssocSemiring α] (f : l ≃. m) (g : m ≃. n) : ((f.trans g).toMatrix
 : Matrix l…
-/
lemma permMatrix_mul [NonAssocSemiring R] :
    (σ * τ).permMatrix R = τ.permMatrix R * σ.permMatrix R := by
  rw [Perm.permMatrix, Perm.mul_def, toPEquiv_trans, PEquiv.toMatrix_trans]

/-- `permMatrix` as a homomorphism. -/
@[simps]
/-
**Matrix.permMatrixHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：permMatrixHom [NonAssocSemiring R] : Perm n ->* Matrix n n R where toFun σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`permMatrix` as a homomorphism.
-/
def permMatrixHom [NonAssocSemiring R] : Perm n →* Matrix n n R where
  toFun σ := σ⁻¹.permMatrix R
  map_one' := permMatrix_one
  map_mul' σ τ := by rw [_root_.mul_inv_rev, permMatrix_mul]

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/--
The l2-operator norm of a permutation matrix is bounded above by 1.
See `Matrix.permMatrix_l2_opNorm_eq` for the equality statement assuming the matrix is nonempty.
-/
/-
**Matrix.permMatrix_l2_opNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permMatrix_l2_opNorm_le : ‖σ.permMatrix 𝕜‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.permMatrix_mulVec`：permMatrix_mulVec {v : n -> R} [CommRing R] : 
σ.permMatrix R *ᵥ v = v ∘ σ
· 使用定理 `EuclideanSpace.norm_eq`：EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n
 : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Equiv.Perm.sum_comp`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → M),   {a | σ a ≠ a} ⊆ ↑s → ∑ x 
∈ s, f (σ…
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The l2-operator norm of a permutation matrix is bounded above by 1.
See `Matrix.permMatrix_l2_opNorm_eq` for the equality statement assuming the mat
rix is nonempty.
-/
theorem permMatrix_l2_opNorm_le : ‖σ.permMatrix 𝕜‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by simp) <| by
    simp [EuclideanSpace.norm_eq, toLpLin_apply, permMatrix_mulVec,
      σ.sum_comp _ (fun i ↦ ‖_‖ ^ 2)]

/--
The l2-operator norm of a nonempty permutation matrix is equal to 1.
Note that this is not true for the empty case, since the empty matrix has l2-operator norm 0.
See `Matrix.permMatrix_l2_opNorm_le` for the inequality version of the empty case.
-/
/-
**Matrix.permMatrix_l2_opNorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permMatrix_l2_opNorm_eq [Nonempty n] : ‖σ.permMatrix 𝕜‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Matrix.permMatrix_l2_opNorm_le`：permMatrix_l2_opNorm_le : ‖σ.permMatrix 
𝕜‖ <= 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `PiLp.continuousLinearEquiv_symm_apply`：∀ (p : ENNReal) (𝕜 : Type u_1) {ι
 : Type u_2} (β : ι → Type u_4) [inst : Semiring 𝕜]   [inst_1 : (i : ι) → AddCom
mGroup (β i)] [inst_2 : (i …
· 使用定理 `EuclideanSpace.norm_eq`：EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n
 : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用引理 `ite_pow`：ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) : (if p then
 a else b) ^ c = if p then a ^ c else b ^ c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The l2-operator norm of a nonempty permutation matrix is equal to 1.
Note that this is not true for the empty case, since the empty matrix has l2-ope
rator norm 0.
See `Matrix.permMatrix_l2_opNorm_le` for the inequality version of the empty cas
e.
-/
theorem permMatrix_l2_opNorm_eq [Nonempty n] : ‖σ.permMatrix 𝕜‖ = 1 :=
  le_antisymm (permMatrix_l2_opNorm_le σ) <| by
    inhabit n
    simpa [EuclideanSpace.norm_eq, permMatrix_mulVec, ← Equiv.eq_symm_apply σ, apply_ite] using
      (σ.permMatrix 𝕜).l2_opNorm_mulVec (WithLp.toLp _ (Pi.single default 1))

end Matrix

