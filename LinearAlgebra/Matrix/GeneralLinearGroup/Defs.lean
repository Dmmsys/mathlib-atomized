/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Ring.Subring.Units

/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the General Linear group `Matrix.GeneralLinearGroup n R`,
consisting of all invertible `n` by `n` `R`-matrices.

## Main definitions

* `Matrix.GeneralLinearGroup` is the type of matrices over R which are units in the matrix ring.
* `Matrix.GLPos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).

## Tags

matrix group, group, matrix inverse
-/

@[expose] public section


namespace Matrix

universe u v

open Matrix

open LinearMap

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices -/
/-
**Matrix.GeneralLinearGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [
Semiring R] : Type _
参数：n : Type u；R : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices
-/
abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [Semiring R] :
    Type _ :=
  (Matrix n n R)ˣ

@[inherit_doc] notation "GL" => GeneralLinearGroup

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable (n) in
/-- Scalar matrix as an element of `GL n R`. -/
/-
**Matrix.GeneralLinearGroup.scalar** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralLine
arGroup`。
形式化陈述：scalar [Semiring R] : Rˣ ->* GL n R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar matrix as an element of `GL n R`.
-/
def scalar [Semiring R] : Rˣ →* GL n R :=
  Units.map (Matrix.scalar n).toMonoidHom

section CoeFnInstance

/-
**Matrix.GeneralLinearGroup.instCoeFun** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.General
LinearGroup`。
形式化陈述：instCoeFun [Semiring R] : CoeFun (GL n R) fun _ => n -> n -> R where coe A
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeFun [Semiring R] : CoeFun (GL n R) fun _ => n → n → R where
  coe A := (A : Matrix n n R)

@[simp]
/-
**Matrix.GeneralLinearGroup.coe_scalar** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.General
LinearGroup`。
形式化陈述：coe_scalar [Semiring R] (u : Rˣ) : ↑(scalar n u) = Matrix.scalar n u.1
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_scalar [Semiring R] (u : Rˣ) : ↑(scalar n u) = Matrix.scalar n u.1 := rfl

end CoeFnInstance

variable [CommRing R]

/-
**Matrix.GeneralLinearGroup.scalar_commute** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Gen
eralLinearGroup`。
形式化陈述：scalar_commute (u : Rˣ) (A : GL n R) : scalar n u * A = A * scalar n u
参数：u : Rˣ；A : GL n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用引理 `Matrix.GeneralLinearGroup.coe_scalar`：coe_scalar [Semiring R] (u : Rˣ) :
 ↑(scalar n u) = Matrix.scalar n u.1
· 使用定理 `Matrix.scalar_comm`：scalar_comm (r : α) (hr : forall r', Commute r r') (
M : Matrix m n α) : scalar m r * M = M * scalar n r
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma scalar_commute (u : Rˣ) (A : GL n R) : scalar n u * A = A * scalar n u := by
  ext : 1
  rw [Units.val_mul, Units.val_mul, coe_scalar, Matrix.scalar_comm _ (Commute.all _)]

/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
/-
**Matrix.GeneralLinearGroup.det** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralLinearG
roup`。
形式化陈述：det : GL n R ->* Rˣ where toFun A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinant of a unit matrix is itself a unit.
-/
def det : GL n R →* Rˣ where
  toFun A :=
    { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
  map_mul' _ _ := Units.ext <| det_mul _ _
/-
**Matrix.GeneralLinearGroup.det_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Genera
lLinearGroup`。
形式化陈述：det_ne_zero [Nontrivial R] (g : GL n R) : g.val.det != 0
参数：g : GL n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
-/
lemma det_ne_zero [Nontrivial R] (g : GL n R) : g.val.det ≠ 0 :=
  g.det.ne_zero

@[simp]
/-
**Matrix.GeneralLinearGroup.det_scalar** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.General
LinearGroup`。
形式化陈述：det_scalar (u : Rˣ) : det (scalar n u) = u ^ Fintype.card n
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_scalar (u : Rˣ) : det (scalar n u) = u ^ Fintype.card n := by
  ext
  simp
/-
**Matrix.GeneralLinearGroup.det_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Gen
eralLinearGroup`。
形式化陈述：det_surjective [Nonempty n] : Function.Surjective (det : GL n R -> Rˣ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_mul_diagonal`：diagonal_mul_diagonal [Fintype n] [Decidab
leEq n] (d₁ d₂ : n -> α) : diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * 
d₂ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Matrix.det_nonsing_inv`：det_nonsing_inv : A⁻¹.det = A.det⁻¹ʳ
· 使用定理 `Units.mk.congr_simp`：∀ {α : Type u} [inst : Monoid α] (val val_1 : α) (e
_val : val = val_1) (inv inv_1 : α) (e_inv : inv = inv_1)   (val_inv : val * inv
 = 1) (in…
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_ite_eq'`：prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : ι -> M) : (∏ x in s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `invOf_units`：invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u 
: α) = ↑u⁻¹
· 使用定理 `Units.mk_val`：mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u
-/
lemma det_surjective [Nonempty n] : Function.Surjective (det : GL n R → Rˣ) := fun r ↦ by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨⟨diagonal fun j ↦ if j = i then r else 1, diagonal fun j ↦ if j = i then r⁻¹.1 else 1,
    ?_, ?_⟩, by simp [det]⟩
  <;> simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.mul_inv, one_mul, mul_one,
      diagonal_eq_one]
  <;> funext j <;> split_ifs <;> simp

/-- The groups `GL n R` (notation for `Matrix.GeneralLinearGroup n R`) and
`LinearMap.GeneralLinearGroup R (n → R)` are multiplicatively equivalent -/
/-
**Matrix.GeneralLinearGroup.toLin** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralLinea
rGroup`。
形式化陈述：toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n -> R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The groups `GL n R` (notation for `Matrix.GeneralLinearGroup n R`) and
`LinearMap.GeneralLinearGroup R (n → R)` are multiplicatively equivalent
-/
def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv toLinAlgEquiv'.toMulEquiv

/-- The isomorphism from `GL n R` to the general linear group of a module
associated with a basis. -/
/-
**Matrix.GeneralLinearGroup.toLin'** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralLine
arGroup`。
形式化陈述：toLin' {V : Type*} [AddCommGroup V] [Module R V] (b : Module.Basis n R V) 
: GL n R ≃* LinearMap.GeneralLinearGroup R V
参数：b : Module.Basis n R V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The isomorphism from `GL n R` to the general linear group of a module
associated with a basis.
-/
noncomputable def toLin'
    {V : Type*} [AddCommGroup V] [Module R V] (b : Module.Basis n R V) :
    GL n R ≃* LinearMap.GeneralLinearGroup R V :=
  toLin.trans <| LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun.symm
/-
**Matrix.GeneralLinearGroup.toLin'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Gener
alLinearGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R] {V : Type u_1}   [inst_3 : AddCommGroup V] [inst_4 : _root_.
Module R V] (b : Module.Basis n R V) (M : GL n R) (v : V),   ((Matrix.GeneralLin
earGroup.toLin' b) M).toLinearEquiv v = (Fintype.linearCombination R ⇑b) ((↑M).m
ulVec ⇑(b.repr v))
参数：b : Module.Basis n R V；M : GL n R；v : V；(Matrix.GeneralLinearGroup.toLin' b) 
M；Fintype.linearCombination R ⇑b；(↑M).mulVec ⇑(b.repr v)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toLin'_apply {V : Type*} [AddCommGroup V] [Module R V]
    (b : Module.Basis n R V) (M : GL n R) (v : V) :
    (toLin' b M).toLinearEquiv v = Fintype.linearCombination R ⇑b (↑M *ᵥ (b.repr v)) := by
  simp [toLin', toLin, Fintype.linearCombination_apply, MulEquiv.trans_apply]

/-- Given a matrix with invertible determinant, we get an element of `GL n R`. -/
@[simps! val]
/-
**Matrix.GeneralLinearGroup.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralLinearG
roup`。
形式化陈述：mk' (A : Matrix n n R) (_ : Invertible (Matrix.det A)) : GL n R
参数：A : Matrix n n R；_ : Invertible (Matrix.det A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a matrix with invertible determinant, we get an element of `GL n R`.
-/
def mk' (A : Matrix n n R) (_ : Invertible (Matrix.det A)) : GL n R :=
  unitOfDetInvertible A

/-- Given a matrix with unit determinant, we get an element of `GL n R`. -/
@[simps! val]
/-
**Matrix.GeneralLinearGroup.mk''** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralLinear
Group`。
形式化陈述：mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R
参数：A : Matrix n n R；h : IsUnit (Matrix.det A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a matrix with unit determinant, we get an element of `GL n R`.
-/
noncomputable def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsingInvUnit A h

/-- Given a matrix with non-zero determinant over a field, we get an element of `GL n K`. -/
@[simps! val]
/-
**Matrix.GeneralLinearGroup.mkOfDetNeZero** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Gene
ralLinearGroup`。
形式化陈述：mkOfDetNeZero {K : Type*} [Field K] (A : Matrix n n K) (h : Matrix.det A !
= 0) : GL n K
参数：A : Matrix n n K；h : Matrix.det A != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a matrix with non-zero determinant over a field, we get an element of `GL 
n K`.
-/
def mkOfDetNeZero {K : Type*} [Field K] (A : Matrix n n K) (h : Matrix.det A ≠ 0) : GL n K :=
  mk' A (invertibleOfNonzero h)
/-
**Matrix.GeneralLinearGroup.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLin
earGroup`。
形式化陈述：ext_iff (A B : GL n R) : A = B ↔ forall i j, (A : Matrix n n R) i j = (B :
 Matrix n n R) i j
参数：A B : GL n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem ext_iff (A B : GL n R) : A = B ↔ ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j :=
  Units.ext_iff.trans Matrix.ext_iff.symm

/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
/-
**Matrix.GeneralLinearGroup.ext** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLinearG
roup`。
形式化陈述：ext ⦃A B : GL n R⦄ (h : forall i j, (A : Matrix n n R) i j = (B : Matrix n
 n R) i j) : A = B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N

--- 原说明 ---
Not marked `@[ext]` as the `ext` tactic already solves this.
-/
theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
  Units.ext <| Matrix.ext h

section CoeLemmas

variable (A B : GL n R)

@[simp]
/-
**Matrix.GeneralLinearGroup.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLin
earGroup`。
形式化陈述：coe_mul : ↑(A * B) = (↑A : Matrix n n R) * (↑B : Matrix n n R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul : ↑(A * B) = (↑A : Matrix n n R) * (↑B : Matrix n n R) :=
  rfl

@[simp]
/-
**Matrix.GeneralLinearGroup.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLin
earGroup`。
形式化陈述：coe_one : ↑(1 : GL n R) = (1 : Matrix n n R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ↑(1 : GL n R) = (1 : Matrix n n R) :=
  rfl
/-
**Matrix.GeneralLinearGroup.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLin
earGroup`。
形式化陈述：coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
-/
theorem coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹ :=
  letI := A.invertible
  invOf_eq_nonsing_inv (↑A : Matrix n n R)

@[simp]
/-
**Matrix.GeneralLinearGroup.coe_toLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralL
inearGroup`。
形式化陈述：coe_toLin : (toLin A : (n -> R) ->ₗ[R] n -> R) = Matrix.mulVecLin A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLin : (toLin A : (n → R) →ₗ[R] n → R) = Matrix.mulVecLin A :=
  rfl

@[simp]
/-
**Matrix.GeneralLinearGroup.toLin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Genera
lLinearGroup`。
形式化陈述：toLin_apply (v : n -> R) : (toLin A : _ -> n -> R) v = Matrix.mulVecLin A 
v
参数：v : n -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLin_apply (v : n → R) : (toLin A : _ → n → R) v = Matrix.mulVecLin A v :=
  rfl

end CoeLemmas

variable {S T : Type*} [CommRing S] [CommRing T]

/-- A ring homomorphism ``f : R →+* S`` induces a homomorphism ``GLₙ(f) : GLₙ(R) →* GLₙ(S)``. -/
@[simps! apply_val]
/-
**Matrix.GeneralLinearGroup.map** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralLinearG
roup`。
形式化陈述：map (f : R ->+* S) : GL n R ->* GL n S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism ``f : R →+* S`` induces a homomorphism ``GLₙ(f) : GLₙ(R) →* 
GLₙ(S)``.
-/
def map (f : R →+* S) : GL n R →* GL n S := Units.map <| (RingHom.mapMatrix f).toMonoidHom

@[simp]
/-
**Matrix.GeneralLinearGroup.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLine
arGroup`。
形式化陈述：map_id : map (RingHom.id R) = MonoidHom.id (GL n R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id : map (RingHom.id R) = MonoidHom.id (GL n R) :=
  rfl

@[simp]
/-
**Matrix.GeneralLinearGroup.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralL
inearGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R] {S : Type u_1}   [inst_3 : CommRing S] (f : R →+* S) (i j : 
n) (g : GL n R), ↑((Matrix.GeneralLinearGroup.map f) g) i j = f (↑g i j)
参数：f : R →+* S；i j : n；g : GL n R；(Matrix.GeneralLinearGroup.map f) g；↑g i j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma map_apply (f : R →+* S) (i j : n) (g : GL n R) : map f g i j = f (g i j) := by
  rfl

@[simp]
/-
**Matrix.GeneralLinearGroup.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLi
nearGroup`。
形式化陈述：map_comp (f : T ->+* R) (g : R ->+* S) : map (g.comp f) = (map g).comp (ma
p (n
参数：f : T ->+* R；g : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp (f : T →+* R) (g : R →+* S) :
    map (g.comp f) = (map g).comp (map (n := n) f) :=
  rfl

@[simp]
/-
**Matrix.GeneralLinearGroup.map_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Gen
eralLinearGroup`。
形式化陈述：map_comp_apply (f : T ->+* R) (g : R ->+* S) (x : GL n T) : (map g).comp (
map f) x = map g (map f x)
参数：f : T ->+* R；g : R ->+* S；x : GL n T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_apply (f : T →+* R) (g : R →+* S) (x : GL n T) :
    (map g).comp (map f) x = map g (map f x) :=
  rfl

variable (f : R →+* S)

@[simp]
/-
**Matrix.GeneralLinearGroup.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLin
earGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R] {S : Type u_1}   [inst_3 : CommRing S] (f : R →+* S), (Matri
x.GeneralLinearGroup.map f) 1 = 1
参数：f : R →+* S；Matrix.GeneralLinearGroup.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_one : map f (1 : GL n R) = 1 := by
  simp only [map_one]
/-
**Matrix.GeneralLinearGroup.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLin
earGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R] {S : Type u_1}   [inst_3 : CommRing S] (f : R →+* S) (g h : 
GL n R),   (Matrix.GeneralLinearGroup.map f) (g * h) = (Matrix.GeneralLinearGrou
p.map f) g * (Matrix.GeneralLinearGroup.map f) h
参数：f : R →+* S；g h : GL n R；Matrix.GeneralLinearGroup.map f；g * h；Matrix.General
LinearGroup.map f；Matrix.GeneralLinearGroup.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_mul (g h : GL n R) : map f (g * h) = map f g * map f h := by
  simp only [map_mul]
/-
**Matrix.GeneralLinearGroup.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLin
earGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R] {S : Type u_1}   [inst_3 : CommRing S] (f : R →+* S) (g : GL
 n R),   (Matrix.GeneralLinearGroup.map f) g⁻¹ = ((Matrix.GeneralLinearGroup.map
 f) g)⁻¹
参数：f : R →+* S；g : GL n R；Matrix.GeneralLinearGroup.map f；(Matrix.GeneralLinearG
roup.map f) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_inv (g : GL n R) : map f g⁻¹ = (map f g)⁻¹ := by
  simp only [map_inv]
/-
**Matrix.GeneralLinearGroup.map_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GeneralLin
earGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R] {S : Type u_1}   [inst_3 : CommRing S] (f : R →+* S) (g : GL
 n R),   Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map f) g) = (
Units.map ↑f) (Matrix.GeneralLinearGroup.det g)
参数：f : R →+* S；g : GL n R；(Matrix.GeneralLinearGroup.map f) g；Units.map ↑f；Matri
x.GeneralLinearGroup.det g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
-/
protected lemma map_det (g : GL n R) : Matrix.GeneralLinearGroup.det (map f g) =
    Units.map f (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp only [map,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Eq.symm (RingHom.map_det f g.1)
/-
**Matrix.GeneralLinearGroup.map_mul_map_inv** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Ge
neralLinearGroup`。
形式化陈述：map_mul_map_inv (g : GL n R) : map f g * map f g⁻¹ = 1
参数：g : GL n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_mul_map_inv (g : GL n R) : map f g * map f g⁻¹ = 1 := by
  simp only [map_inv, mul_inv_cancel]
/-
**Matrix.GeneralLinearGroup.map_inv_mul_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Ge
neralLinearGroup`。
形式化陈述：map_inv_mul_map (g : GL n R) : map f g⁻¹ * map f g = 1
参数：g : GL n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_inv_mul_map (g : GL n R) : map f g⁻¹ * map f g = 1 := by
  simp only [map_inv, inv_mul_cancel]

@[simp]
/-
**Matrix.GeneralLinearGroup.coe_map_mul_map_inv** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x.GeneralLinearGroup`。
形式化陈述：coe_map_mul_map_inv (g : GL n R) : g.val.map f * g.val⁻¹.map f = 1
参数：g : GL n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.map_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} {β : Type w} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L 
: Ma…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
lemma coe_map_mul_map_inv (g : GL n R) : g.val.map f * g.val⁻¹.map f = 1 := by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, mul_nonsing_inv, map_zero, map_one, Matrix.map_one]

@[simp]
/-
**Matrix.GeneralLinearGroup.coe_map_inv_mul_map** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x.GeneralLinearGroup`。
形式化陈述：coe_map_inv_mul_map (g : GL n R) : g.val⁻¹.map f * g.val.map f = 1
参数：g : GL n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.map_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} {β : Type w} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L 
: Ma…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
lemma coe_map_inv_mul_map (g : GL n R) : g.val⁻¹.map f * g.val.map f = 1 := by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, nonsing_inv_mul, map_zero, map_one, Matrix.map_one]
/-
**Matrix.GeneralLinearGroup.map_scalar** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.General
LinearGroup`。
形式化陈述：map_scalar (u : Rˣ) : map f (scalar n u) = scalar n (Units.map f u)
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.map_apply`：∀ {n : Type u} [inst : DecidableEq 
n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   [ins
t_3 : CommRing S] (f : R …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma map_scalar (u : Rˣ) : map f (scalar n u) = scalar n (Units.map f u) := by
  ext
  simp [Matrix.diagonal_apply]
  split <;> simp

section kronecker
variable {R m : Type*} [CommSemiring R] [Fintype m] [DecidableEq m]

open scoped Kronecker

/-- The invertible kronecker matrix of invertible matrices. -/
/-
**Matrix.GeneralLinearGroup.kronecker** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralL
inearGroup`。
形式化陈述：{n : Type u} →   [inst : DecidableEq n] →     [inst_1 : Fintype n] →      
 {R : Type u_3} →         {m : Type u_4} →           [inst_2 : CommSemiring R] →
 [inst_3 : Fintype m] → [inst_4 : DecidableEq m] → GL n R → GL m R → GL (n × m) 
R
参数：n × m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The invertible kronecker matrix of invertible matrices.
-/
protected def kronecker (x : GL n R) (y : GL m R) : GL (n × m) R where
  val := x ⊗ₖ y
  inv := ↑x⁻¹ ⊗ₖ ↑y⁻¹
  val_inv := by simp only [← mul_kronecker_mul, Units.mul_inv, one_kronecker_one]
  inv_val := by simp only [← mul_kronecker_mul, Units.inv_mul, one_kronecker_one]
/-
**Matrix.GeneralLinearGroup._root_.Matrix.IsUnit.kronecker** 是 Mathlib 中的一个定理，位于
命名空间 `Matrix.GeneralLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.IsUnit.kronecker {x : Matrix n n R} {y : Matrix m m R}
    (hx : IsUnit x) (hy : IsUnit y) : IsUnit (x ⊗ₖ y) :=
  GeneralLinearGroup.kronecker hx.unit hy.unit |>.isUnit

end kronecker

end GeneralLinearGroup

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

/-- `toGL` is the map from the special linear group to the general linear group. -/
/-
**Matrix.SpecialLinearGroup.toGL** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.SpecialLinear
Group`。
形式化陈述：toGL : Matrix.SpecialLinearGroup n R ->* Matrix.GeneralLinearGroup n R whe
re toFun A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toGL` is the map from the special linear group to the general linear group.
-/
def toGL : Matrix.SpecialLinearGroup n R →* Matrix.GeneralLinearGroup n R where
  toFun A := ⟨↑A, ↑A⁻¹, congr_arg (·.1) (mul_inv_cancel A), congr_arg (·.1) (inv_mul_cancel A)⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl
/-
**Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup** 是 Mathlib 中的一个实例，位于命名空间
 `Matrix.SpecialLinearGroup`。
形式化陈述：hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R) :=
  ⟨toGL⟩
/-
**Matrix.SpecialLinearGroup.toGL_injective** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Spe
cialLinearGroup`。
形式化陈述：toGL_injective : Function.Injective (toGL : SpecialLinearGroup n R -> GL n
 R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Units.mk.injEq`：∀ {α : Type u} [inst : Monoid α] (val inv : α) (val_inv 
: val * inv = 1) (inv_val : inv * val = 1) (val_1 inv_1 : α)   (val_inv_1 : val_
1 * …
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma toGL_injective :
    Function.Injective (toGL : SpecialLinearGroup n R → GL n R) := fun g g' ↦ by
  simpa [toGL] using! fun h _ ↦ Subtype.ext h

@[simp]
/-
**Matrix.SpecialLinearGroup.toGL_inj** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialLi
nearGroup`。
形式化陈述：toGL_inj (g g' : SpecialLinearGroup n R) : (g : GeneralLinearGroup n R) = 
g' ↔ g = g'
参数：g g' : SpecialLinearGroup n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Matrix.SpecialLinearGroup.toGL_injective`：toGL_injective : Function.Inje
ctive (toGL : SpecialLinearGroup n R -> GL n R)
-/
lemma toGL_inj (g g' : SpecialLinearGroup n R) :
    (g : GeneralLinearGroup n R) = g' ↔ g = g' :=
  toGL_injective.eq_iff

@[simp]
/-
**Matrix.SpecialLinearGroup.coeToGL_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Specia
lLinearGroup`。
形式化陈述：coeToGL_det (g : SpecialLinearGroup n R) : Matrix.GeneralLinearGroup.det (
g : GL n R) = 1
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coeToGL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det (g : GL n R) = 1 :=
  Units.ext g.prop

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_GL_coe_matrix** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.
SpecialLinearGroup`。
形式化陈述：coe_GL_coe_matrix (g : SpecialLinearGroup n R) : ((toGL g) : Matrix n n R)
 = g
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_GL_coe_matrix (g : SpecialLinearGroup n R) : ((toGL g) : Matrix n n R) = g := rfl

variable (S) in
/-- `mapGL` is the map from the special linear group over `R` to the general linear group over
`S`, where `S` is an `R`-algebra. -/
/-
**Matrix.SpecialLinearGroup.mapGL** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.SpecialLinea
rGroup`。
形式化陈述：mapGL : Matrix.SpecialLinearGroup n R ->* Matrix.GeneralLinearGroup n S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapGL` is the map from the special linear group over `R` to the general linear 
group over
`S`, where `S` is an `R`-algebra.
-/
def mapGL : Matrix.SpecialLinearGroup n R →* Matrix.GeneralLinearGroup n S :=
  toGL.comp (map (algebraMap R S))

@[simp]
/-
**Matrix.SpecialLinearGroup.mapGL_inj** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialL
inearGroup`。
形式化陈述：mapGL_inj [FaithfulSMul R S] (g g' : SpecialLinearGroup n R) : mapGL S g =
 mapGL S g' ↔ g = g'
参数：g g' : SpecialLinearGroup n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mapGL_inj [FaithfulSMul R S] (g g' : SpecialLinearGroup n R) :
    mapGL S g = mapGL S g' ↔ g = g' := by
  simp [mapGL, ext_iff]
/-
**Matrix.SpecialLinearGroup.mapGL_injective** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Sp
ecialLinearGroup`。
形式化陈述：mapGL_injective [FaithfulSMul R S] : Function.Injective (mapGL (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma mapGL_injective [FaithfulSMul R S] :
    Function.Injective (mapGL (R := R) (n := n) S) :=
  fun a b ↦ by simp

@[simp]
/-
**Matrix.SpecialLinearGroup.mapGL_coe_matrix** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：mapGL_coe_matrix (g : SpecialLinearGroup n R) : ((mapGL S g) : Matrix n n 
S) = g.map (algebraMap R S)
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapGL_coe_matrix (g : SpecialLinearGroup n R) :
    ((mapGL S g) : Matrix n n S) = g.map (algebraMap R S) :=
  rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.map_mapGL** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialL
inearGroup`。
形式化陈述：map_mapGL {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTo
wer R S T] (g : SpecialLinearGroup n R) : (mapGL S g).map (algebraMap S T) = map
GL T g
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.map_apply`：∀ {n : Type u} [inst : DecidableEq 
n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   [ins
t_3 : CommRing S] (f : R …
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_mapGL {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : SpecialLinearGroup n R) :
    (mapGL S g).map (algebraMap S T) = mapGL T g := by
  ext
  simp [IsScalarTower.algebraMap_apply R S T]

@[simp]
/-
**Matrix.SpecialLinearGroup.det_mapGL** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialL
inearGroup`。
形式化陈述：det_mapGL (g : SpecialLinearGroup n R) : (mapGL S g).det = 1
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma det_mapGL (g : SpecialLinearGroup n R) : (mapGL S g).det = 1 := by
  simp [mapGL]

end SpecialLinearGroup

section

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

section

variable (n R)

/-- This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant. -/
/-
**Matrix.GLPos** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：GLPos : Subgroup (GL n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant.
-/
def GLPos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap GeneralLinearGroup.det

@[inherit_doc] scoped[MatrixGroups] notation "GL(" n ", " R ")" "⁺" => GLPos (Fin n) R

end

@[simp]
/-
**Matrix.mem_glpos** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_glpos (A : GL n R) : A in GLPos n R ↔ 0 < (Matrix.GeneralLinearGroup.d
et A : R)
参数：A : GL n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_glpos (A : GL n R) : A ∈ GLPos n R ↔ 0 < (Matrix.GeneralLinearGroup.det A : R) :=
  Iff.rfl
/-
**Matrix.GLPos.det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GLPos`。
形式化陈述：∀ {n : Type u} {R : Type v} [inst : DecidableEq n] [inst_1 : Fintype n] [i
nst_2 : CommRing R] [inst_3 : LinearOrder R]   [inst_4 : IsStrictOrderedRing R] 
(A : ↥(Matrix.GLPos n R)), (↑↑A).det ≠ 0
参数：A : ↥(Matrix.GLPos n R)；↑↑A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem GLPos.det_ne_zero (A : GLPos n R) : ((A : GL n R) : Matrix n n R).det ≠ 0 :=
  ne_of_gt A.prop

end

section Neg

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on general linear group on even cardinality `n` given by negating
each element. -/
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal operation of negation on general linear group on even cardinality `n` giv
en by negating
each element.
-/
instance : Neg (GLPos n R) :=
  ⟨fun g =>
    ⟨-g, by
      rw [mem_glpos, GeneralLinearGroup.val_det_apply, Units.val_neg, det_neg,
        (Fact.out (p := Even <| Fintype.card n)).neg_one_pow, one_mul]
      exact g.prop⟩⟩

@[simp]
/-
**Matrix.GLPos.coe_neg_GL** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GLPos`。
形式化陈述：∀ {n : Type u} {R : Type v} [inst : DecidableEq n] [inst_1 : Fintype n] [i
nst_2 : CommRing R] [inst_3 : LinearOrder R]   [inst_4 : IsStrictOrderedRing R] 
[inst_5 : Fact (Even (Fintype.card n))] (g : ↥(Matrix.GLPos n R)), ↑(-g) = -↑g
参数：Even (Fintype.card n)；g : ↥(Matrix.GLPos n R)；-g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GLPos.coe_neg_GL (g : GLPos n R) : ↑(-g) = -(g : GL n R) :=
  rfl

@[simp]
/-
**Matrix.GLPos.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GLPos`。
形式化陈述：∀ {n : Type u} {R : Type v} [inst : DecidableEq n] [inst_1 : Fintype n] [i
nst_2 : CommRing R] [inst_3 : LinearOrder R]   [inst_4 : IsStrictOrderedRing R] 
[inst_5 : Fact (Even (Fintype.card n))] (g : ↥(Matrix.GLPos n R)), ↑↑(-g) = -↑↑g
参数：Even (Fintype.card n)；g : ↥(Matrix.GLPos n R)；-g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GLPos.coe_neg (g : GLPos n R) : (↑(-g) : GL n R) = -((g : GL n R) : Matrix n n R) :=
  rfl

@[simp]
/-
**Matrix.GLPos.coe_neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.GLPos`。
形式化陈述：∀ {n : Type u} {R : Type v} [inst : DecidableEq n] [inst_1 : Fintype n] [i
nst_2 : CommRing R] [inst_3 : LinearOrder R]   [inst_4 : IsStrictOrderedRing R] 
[inst_5 : Fact (Even (Fintype.card n))] (g : ↥(Matrix.GLPos n R)) (i j : n),   ↑
↑(-g) i j = -↑↑g i j
参数：Even (Fintype.card n)；g : ↥(Matrix.GLPos n R)；i j : n；-g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GLPos.coe_neg_apply (g : GLPos n R) (i j : n) :
    ((↑(-g) : GL n R) : Matrix n n R) i j = -((g : GL n R) : Matrix n n R) i j :=
  rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDistribNeg (GLPos n R) :=
  Subtype.coe_injective.hasDistribNeg _ GLPos.coe_neg_GL (GLPos n R).coe_mul

end Neg

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n]
  {R : Type v} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `Matrix.SpecialLinearGroup n R` embeds into `GL_pos n R` -/
/-
**Matrix.SpecialLinearGroup.toGLPos** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：toGLPos : SpecialLinearGroup n R ->* GLPos n R where toFun A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.SpecialLinearGroup n R` embeds into `GL_pos n R`
-/
def toGLPos : SpecialLinearGroup n R →* GLPos n R where
  toFun A := ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩
  map_one' := Subtype.ext <| Units.ext <| rfl
  map_mul' _ _ := Subtype.ext <| Units.ext <| rfl
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (SpecialLinearGroup n R) (GLPos n R) :=
  ⟨toGLPos⟩
/-
**Matrix.SpecialLinearGroup.toGLPos_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.
SpecialLinearGroup`。
形式化陈述：toGLPos_injective : Function.Injective (toGLPos : SpecialLinearGroup n R -
> GLPos n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem toGLPos_injective : Function.Injective (toGLPos : SpecialLinearGroup n R → GLPos n R) :=
  -- Porting note: had to rewrite this to hint the correct types to Lean
  -- (It can't find the coercion GLPos n R → Matrix n n R)
  Function.Injective.of_comp
    (f := fun (A : GLPos n R) ↦ ((A : GL n R) : Matrix n n R))
    Subtype.coe_injective

/-- Coercing a `Matrix.SpecialLinearGroup` via `GL_pos` and `GL` is the same as coercing straight to
a matrix. -/
@[simp]
/-
**Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix** 是 Mathlib 中的一个定理，位于命名空
间 `Matrix.SpecialLinearGroup`。
形式化陈述：coe_GLPos_coe_GL_coe_matrix (g : SpecialLinearGroup n R) : (↑(↑(↑g : GLPos
 n R) : GL n R) : Matrix n n R) = ↑g
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercing a `Matrix.SpecialLinearGroup` via `GL_pos` and `GL` is the same as coer
cing straight to
a matrix.
-/
theorem coe_GLPos_coe_GL_coe_matrix (g : SpecialLinearGroup n R) :
    (↑(↑(↑g : GLPos n R) : GL n R) : Matrix n n R) = ↑g :=
  rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_to_GLPos_to_GL_det** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix.SpecialLinearGroup`。
形式化陈述：coe_to_GLPos_to_GL_det (g : SpecialLinearGroup n R) : Matrix.GeneralLinear
Group.det ((g : GLPos n R) : GL n R) = 1
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coe_to_GLPos_to_GL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det ((g : GLPos n R) : GL n R) = 1 :=
  Units.ext g.prop

variable [Fact (Even (Fintype.card n))]

@[norm_cast]
/-
**Matrix.SpecialLinearGroup.coe_GLPos_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Spec
ialLinearGroup`。
形式化陈述：coe_GLPos_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(↑g : GLPos n R)
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem coe_GLPos_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(↑g : GLPos n R) :=
  Subtype.ext <| Units.ext rfl

end SpecialLinearGroup

end Matrix

