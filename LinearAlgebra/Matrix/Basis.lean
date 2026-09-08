/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Bases and matrices

This file defines the map `Basis.toMatrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

* `Basis.toMatrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
* `basis.toMatrixEquiv` is `Basis.toMatrix` bundled as a linear equiv

## Main results

* `LinearMap.toMatrix_id_eq_basis_toMatrix`: `LinearMap.toMatrix b c id`
  is equal to `Basis.toMatrix b c`
* `Basis.toMatrix_mul_toMatrix`: multiplying `Basis.toMatrix` with another
  `Basis.toMatrix` gives a `Basis.toMatrix`

## Tags

matrix, basis
-/

@[expose] public section


noncomputable section

open Function LinearMap Matrix Module Set Submodule

variable {ι ι' κ κ' : Type*}
variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

namespace Module.Basis

/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
/-
**Module.Basis.toMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix (e : Basis ι R M) (v : ι' -> M) : Matrix ι ι' R
参数：e : Basis ι R M；v : ι' -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix w
hose columns
are the vectors `v i` written in the basis `e`.
-/
def toMatrix (e : Basis ι R M) (v : ι' → M) : Matrix ι ι' R := fun i j ↦ e.repr (v j) i

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')
/-
**Module.Basis.toMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_apply : e.toMatrix v i j = e.repr (v j) i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMatrix_apply : e.toMatrix v i j = e.repr (v j) i :=
  rfl
/-
**Module.Basis.toMatrix_transpose_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`
。
形式化陈述：toMatrix_transpose_apply : (e.toMatrix v)ᵀ j = e.repr (v j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem toMatrix_transpose_apply : (e.toMatrix v)ᵀ j = e.repr (v j) :=
  funext fun _ => rfl
/-
**Module.Basis.toMatrix_eq_toMatrix_constr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Bas
is`。
形式化陈述：toMatrix_eq_toMatrix_constr [Fintype ι] [DecidableEq ι] (v : ι -> M) : e.t
oMatrix v = LinearMap.toMatrix e e (e.constr Nat v)
参数：v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toMatrix_apply`：toMatrix_apply : e.toMatrix v i j = e.repr 
(v j) i
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
-/
theorem toMatrix_eq_toMatrix_constr [Fintype ι] [DecidableEq ι] (v : ι → M) :
    e.toMatrix v = LinearMap.toMatrix e e (e.constr ℕ v) := by
  ext
  rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Basis.constr_basis]

-- TODO (maybe) Adjust the definition of `Basis.toMatrix` to eliminate the transpose.
/-
**Module.Basis.coePiBasisFun.toMatrix_eq_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Mo
dule.Basis.coePiBasisFun`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_5} [inst : CommSemiring R] [inst_1 : Finite ι
],   (Pi.basisFun R ι).toMatrix = Matrix.transpose
参数：Pi.basisFun R ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem coePiBasisFun.toMatrix_eq_transpose [Finite ι] :
    ((Pi.basisFun R ι).toMatrix : Matrix ι ι R → Matrix ι ι R) = Matrix.transpose := by
  ext M i j
  rfl

@[simp]
/-
**Module.Basis.toMatrix_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_self [DecidableEq ι] : e.toMatrix e = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_self [DecidableEq ι] : e.toMatrix e = 1 := by
  unfold Basis.toMatrix
  ext i j
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
/-
**Module.Basis.toMatrix_update** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_update [DecidableEq ι'] (x : M) : e.toMatrix (Function.update v j
 x) = Matrix.updateCol (e.toMatrix v) j (e.repr x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toMatrix.eq_1`：∀ {ι : Type u_1} {ι' : Type u_2} {R : Type u
_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: _root_.Module …
· 使用定理 `Matrix.updateCol_apply`：updateCol_apply [DecidableEq n] {j' : n} : updat
eCol M j c i j' = if j' = j then c i else M i j'
· 使用定理 `Module.Basis.toMatrix_apply`：toMatrix_apply : e.toMatrix v i j = e.repr 
(v j) i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem toMatrix_update [DecidableEq ι'] (x : M) :
    e.toMatrix (Function.update v j x) = Matrix.updateCol (e.toMatrix v) j (e.repr x) := by
  ext i' k
  rw [Basis.toMatrix, Matrix.updateCol_apply, e.toMatrix_apply]
  split_ifs with h
  · rw [h, update_self j x v]
  · rw [update_of_ne h]

set_option backward.isDefEq.respectTransparency false in
/-- The basis constructed by `unitsSMul` has vectors given by a diagonal matrix. -/
@[simp]
/-
**Module.Basis.toMatrix_unitsSMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_unitsSMul [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι -> R₂ˣ) : e.
toMatrix (e.unitsSMul w) = diagonal ((↑) ∘ w)
参数：e : Basis ι R₂ M₂；w : ι -> R₂ˣ。
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
· 使用定理 `Module.Basis.unitsSMul_apply`：unitsSMul_apply {v : Basis ι R M} {w : ι -
> Rˣ} (i : ι) : unitsSMul v w i = w i • v i
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
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0

--- 原说明 ---
The basis constructed by `unitsSMul` has vectors given by a diagonal matrix.
-/
theorem toMatrix_unitsSMul [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι → R₂ˣ) :
    e.toMatrix (e.unitsSMul w) = diagonal ((↑) ∘ w) := by
  ext i j
  by_cases h : i = j <;>
    simp [h, toMatrix_apply, unitsSMul_apply, Units.smul_def]

/-- The basis constructed by `isUnitSMul` has vectors given by a diagonal matrix. -/
@[simp]
/-
**Module.Basis.toMatrix_isUnitSMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_isUnitSMul [DecidableEq ι] (e : Basis ι R₂ M₂) {w : ι -> R₂} (hw 
: forall i, IsUnit (w i)) : e.toMatrix (e.isUnitSMul hw) = diagonal w
参数：e : Basis ι R₂ M₂；hw : forall i, IsUnit (w i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.toMatrix_unitsSMul`：toMatrix_unitsSMul [DecidableEq ι] (e :
 Basis ι R₂ M₂) (w : ι -> R₂ˣ) : e.toMatrix (e.unitsSMul w) = diagonal ((↑) ∘ w)

--- 原说明 ---
The basis constructed by `isUnitSMul` has vectors given by a diagonal matrix.
-/
theorem toMatrix_isUnitSMul [DecidableEq ι] (e : Basis ι R₂ M₂) {w : ι → R₂}
    (hw : ∀ i, IsUnit (w i)) : e.toMatrix (e.isUnitSMul hw) = diagonal w :=
  e.toMatrix_unitsSMul _
/-
**Module.Basis.toMatrix_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_smul_left {G} [Group G] [DistribMulAction G M] [SMulCommClass G R
 M] (g : G) : (g • e).toMatrix v = e.toMatrix (g⁻¹ • v)
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMatrix_smul_left {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M] (g : G) :
    (g • e).toMatrix v = e.toMatrix (g⁻¹ • v) := rfl

@[simp]
/-
**Module.Basis.sum_toMatrix_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sum_toMatrix_smul_self [Fintype ι] : ∑ i : ι, e.toMatrix v i j • e i = v j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.toMatrix_apply`：toMatrix_apply : e.toMatrix v i j = e.repr 
(v j) i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_toMatrix_smul_self [Fintype ι] : ∑ i : ι, e.toMatrix v i j • e i = v j := by
  simp_rw [e.toMatrix_apply, e.sum_repr]
/-
**Module.Basis.toMatrix_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_smul {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S]
 [Fintype ι] [DecidableEq ι] (x : S) (b : Basis ι R₁ S) (w : ι -> S) : (b.toMatr
ix (x • w)) = (Algebra.leftMulMatrix b x) * (b.toMatrix w)
参数：x : S；b : Basis ι R₁ S；w : ι -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toMatrix_apply`：toMatrix_apply : e.toMatrix v i j = e.repr 
(v j) i
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.leftMulMatrix_mulVec_repr`：leftMulMatrix_mulVec_repr (x y : S) :
 leftMulMatrix b x *ᵥ b.repr y = b.repr (x * y)
-/
theorem toMatrix_smul {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S] [Fintype ι]
    [DecidableEq ι] (x : S) (b : Basis ι R₁ S) (w : ι → S) :
    (b.toMatrix (x • w)) = (Algebra.leftMulMatrix b x) * (b.toMatrix w) := by
  ext
  rw [Basis.toMatrix_apply, Pi.smul_apply, smul_eq_mul, ← Algebra.leftMulMatrix_mulVec_repr]
  rfl
/-
**Module.Basis.toMatrix_map_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_map_vecMul {S : Type*} [Semiring S] [Algebra R S] [Fintype ι] (b 
: Basis ι R S) (v : ι' -> S) : b ᵥ* ((b.toMatrix v).map <| algebraMap R S) = v
参数：b : Basis ι R S；v : ι' -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.sum_toMatrix_smul_self`：sum_toMatrix_smul_self [Fintype ι] 
: ∑ i : ι, e.toMatrix v i j • e i = v j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_map_vecMul {S : Type*} [Semiring S] [Algebra R S] [Fintype ι] (b : Basis ι R S)
    (v : ι' → S) : b ᵥ* ((b.toMatrix v).map <| algebraMap R S) = v := by
  ext i
  simp_rw [vecMul, dotProduct, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def,
    sum_toMatrix_smul_self]

@[simp]
/-
**Module.Basis.toLin_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toLin_toMatrix [Finite ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M)
 : Matrix.toLin v e (e.toMatrix v) = LinearMap.id
参数：v : Basis ι' R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.toLin_self`：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i :
 n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用定理 `Module.Basis.sum_toMatrix_smul_self`：sum_toMatrix_smul_self [Fintype ι] 
: ∑ i : ι, e.toMatrix v i j • e i = v j
-/
theorem toLin_toMatrix [Finite ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M) :
    Matrix.toLin v e (e.toMatrix v) = LinearMap.id :=
  v.ext fun i => by cases nonempty_fintype ι; rw [toLin_self, id_apply, e.sum_toMatrix_smul_self]

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
/-
**Module.Basis.toMatrixEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：toMatrixEquiv [Fintype ι] (e : Basis ι R M) : (ι -> M) ≃ₗ[R] Matrix ι ι R 
where toFun
参数：e : Basis ι R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a basis `e : ι → M`, build a linear equivalence between families of vectors
 `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in t
he basis `e`.
-/
def toMatrixEquiv [Fintype ι] (e : Basis ι R M) : (ι → M) ≃ₗ[R] Matrix ι ι R where
  toFun := e.toMatrix
  map_add' v w := by
    ext i j
    rw [Matrix.add_apply, e.toMatrix_apply, Pi.add_apply, map_add]
    rfl
  map_smul' := by
    intro c v
    ext i j
    rw [e.toMatrix_apply, Pi.smul_apply, map_smul]
    rfl
  invFun m j := ∑ i, m i j • e i
  left_inv := by
    intro v
    ext j
    exact e.sum_toMatrix_smul_self v j
  right_inv := by
    intro m
    ext k l
    simp only [e.toMatrix_apply, ← e.equivFun_apply, ← e.equivFun_symm_apply,
      LinearEquiv.apply_symm_apply]

variable (R₂) in
/-
**Module.Basis.restrictScalars_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`
。
形式化陈述：restrictScalars_toMatrix [Fintype ι] [DecidableEq ι] {S : Type*} [CommRing
 S] [Nontrivial S] [Algebra R₂ S] [Module S M₂] [IsScalarTower R₂ S M₂] [IsDomai
n R₂] [IsTorsionFree R₂ S] (b : Basis ι S M₂) (v : ι -> span R₂ (Set.range b)) :
 (algebraMap R₂ S).mapMatrix ((b.restrictScalars R₂).toMatrix v) = b.toMatrix (f
un i => (v i : M₂))
参数：b : Basis ι S M₂；v : ι -> span R₂ (Set.range b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.map_apply`：map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j :
 n} : M.map f i j = f (M i j)
· 使用定理 `Module.Basis.toMatrix_apply`：toMatrix_apply : e.toMatrix v i j = e.repr 
(v j) i
· 使用定理 `Module.Basis.restrictScalars_repr_apply`：∀ {ι : Type u_1} (R : Type u_3)
 {M : Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst
_2 : Ring S] [inst_3 : Nontri…
-/
theorem restrictScalars_toMatrix [Fintype ι] [DecidableEq ι] {S : Type*} [CommRing S] [Nontrivial S]
    [Algebra R₂ S] [Module S M₂] [IsScalarTower R₂ S M₂] [IsDomain R₂] [IsTorsionFree R₂ S]
    (b : Basis ι S M₂) (v : ι → span R₂ (Set.range b)) :
    (algebraMap R₂ S).mapMatrix ((b.restrictScalars R₂).toMatrix v) =
      b.toMatrix (fun i ↦ (v i : M₂)) := by
  ext
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply,
    Basis.restrictScalars_repr_apply, Basis.toMatrix_apply]

end Module.Basis

section MulLinearMapToMatrix

variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)
variable (f : M →ₗ[R] N)

open LinearMap

section Fintype

/-- A generalization of `LinearMap.toMatrix_id`. -/
@[simp]
/-
**LinearMap.toMatrix_id_eq_basis_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_id_eq_basis_toMatrix [Fintype ι] [DecidableEq ι] [Finit
e ι'] : LinearMap.toMatrix b b' id = b'.toMatrix b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i

--- 原说明 ---
A generalization of `LinearMap.toMatrix_id`.
-/
theorem LinearMap.toMatrix_id_eq_basis_toMatrix [Fintype ι] [DecidableEq ι] [Finite ι'] :
    LinearMap.toMatrix b b' id = b'.toMatrix b := by
  ext i
  apply LinearMap.toMatrix_apply

variable [Fintype ι']

@[simp]
/-
**basis_toMatrix_mul_linearMap_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：basis_toMatrix_mul_linearMap_toMatrix [Finite κ] [Fintype κ'] [DecidableEq
 ι'] : c.toMatrix c' * LinearMap.toMatrix b' c' f = LinearMap.toMatrix b' c f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_toMatrix`：Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) : Matrix
.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
· 使用定理 `Module.Basis.toLin_toMatrix`：toLin_toMatrix [Finite ι] [Fintype ι'] [Dec
idableEq ι'] (v : Basis ι' R M) : Matrix.toLin v e (e.toMatrix v) = LinearMap.id
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
-/
theorem basis_toMatrix_mul_linearMap_toMatrix [Finite κ] [Fintype κ'] [DecidableEq ι'] :
    c.toMatrix c' * LinearMap.toMatrix b' c' f = LinearMap.toMatrix b' c f :=
  (Matrix.toLin b' c).injective <| by
    have := Classical.decEq κ'
    rw [toLin_toMatrix, toLin_mul b' c' c, toLin_toMatrix, c.toLin_toMatrix, LinearMap.id_comp]
/-
**basis_toMatrix_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：basis_toMatrix_mul [Fintype κ] [Finite ι] [DecidableEq κ] (b₁ : Basis ι R 
M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N) (A : Matrix ι' κ R) : b₁.toMatrix b₂ *
 A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A)
参数：b₁ : Basis ι R M；b₂ : Basis ι' R M；b₃ : Basis κ R N；A : Matrix ι' κ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `basis_toMatrix_mul_linearMap_toMatrix`：basis_toMatrix_mul_linearMap_toMa
trix [Finite κ] [Fintype κ'] [DecidableEq ι'] : c.toMatrix c' * LinearMap.toMatr
ix b' c' f = LinearMap.toMa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_toLin`：LinearMap.toMatrix_toLin (M : Matrix m n R) : 
LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M
-/
theorem basis_toMatrix_mul [Fintype κ] [Finite ι] [DecidableEq κ]
    (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N) (A : Matrix ι' κ R) :
    b₁.toMatrix b₂ * A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A) := by
  have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  rwa [LinearMap.toMatrix_toLin] at this

variable [Finite κ] [Fintype ι]

@[simp]
/-
**linearMap_toMatrix_mul_basis_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearMap_toMatrix_mul_basis_toMatrix [Finite κ'] [DecidableEq ι] [Decidab
leEq ι'] : LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c' 
f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_toMatrix`：Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) : Matrix
.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
· 使用定理 `Module.Basis.toLin_toMatrix`：toLin_toMatrix [Finite ι] [Fintype ι'] [Dec
idableEq ι'] (v : Basis ι' R M) : Matrix.toLin v e (e.toMatrix v) = LinearMap.id
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
-/
theorem linearMap_toMatrix_mul_basis_toMatrix [Finite κ'] [DecidableEq ι] [DecidableEq ι'] :
    LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c' f :=
  (Matrix.toLin b c').injective <| by
    rw [toLin_toMatrix, toLin_mul b b' c', toLin_toMatrix, b'.toLin_toMatrix, LinearMap.comp_id]
/-
**basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix [Fintype κ'] [Dec
idableEq ι] [DecidableEq ι'] : c.toMatrix c' * LinearMap.toMatrix b' c' f * b'.t
oMatrix b = LinearMap.toMatrix b c f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `basis_toMatrix_mul_linearMap_toMatrix`：basis_toMatrix_mul_linearMap_toMa
trix [Finite κ] [Fintype κ'] [DecidableEq ι'] : c.toMatrix c' * LinearMap.toMatr
ix b' c' f = LinearMap.toMa…
· 使用定理 `linearMap_toMatrix_mul_basis_toMatrix`：linearMap_toMatrix_mul_basis_toMa
trix [Finite κ'] [DecidableEq ι] [DecidableEq ι'] : LinearMap.toMatrix b' c' f *
 b'.toMatrix b = LinearMap.…
-/
theorem basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    [Fintype κ'] [DecidableEq ι] [DecidableEq ι'] :
    c.toMatrix c' * LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c f := by
  cases nonempty_fintype κ
  rw [basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix]
/-
**mul_basis_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] (b₁ : Basis ι R M) (b₂
 : Basis ι' R M) (b₃ : Basis κ R N) (A : Matrix κ ι R) : A * b₁.toMatrix b₂ = Li
nearMap.toMatrix b₂ b₃ (toLin b₁ b₃ A)
参数：b₁ : Basis ι R M；b₂ : Basis ι' R M；b₃ : Basis κ R N；A : Matrix κ ι R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `linearMap_toMatrix_mul_basis_toMatrix`：linearMap_toMatrix_mul_basis_toMa
trix [Finite κ'] [DecidableEq ι] [DecidableEq ι'] : LinearMap.toMatrix b' c' f *
 b'.toMatrix b = LinearMap.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_toLin`：LinearMap.toMatrix_toLin (M : Matrix m n R) : 
LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M
-/
theorem mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] (b₁ : Basis ι R M) (b₂ : Basis ι' R M)
    (b₃ : Basis κ R N) (A : Matrix κ ι R) :
    A * b₁.toMatrix b₂ = LinearMap.toMatrix b₂ b₃ (toLin b₁ b₃ A) := by
  cases nonempty_fintype κ
  have := linearMap_toMatrix_mul_basis_toMatrix b₂ b₁ b₃ (Matrix.toLin b₁ b₃ A)
  rwa [LinearMap.toMatrix_toLin] at this
/-
**basis_toMatrix_basisFun_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：basis_toMatrix_basisFun_mul (b : Basis ι R (ι -> R)) (A : Matrix ι ι R) : 
b.toMatrix (Pi.basisFun R ι) * A = of fun i j => b.repr (A.col j) i
参数：b : Basis ι R (ι -> R)；A : Matrix ι ι R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `basis_toMatrix_mul`：basis_toMatrix_mul [Fintype κ] [Finite ι] [Decidable
Eq κ] (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N) (A : Matrix ι' κ
 R) : b₁…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.toLin'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type 
u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix 
m n R) (v…
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用定理 `Matrix.mulVec_single_one`：mulVec_single_one [Fintype n] [DecidableEq n] 
[NonAssocSemiring R] (M : Matrix m n R) (j : n) : M *ᵥ Pi.single j 1 = M.col j
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
-/
theorem basis_toMatrix_basisFun_mul (b : Basis ι R (ι → R)) (A : Matrix ι ι R) :
    b.toMatrix (Pi.basisFun R ι) * A = of fun i j => b.repr (A.col j) i := by
  classical
  simp only [basis_toMatrix_mul _ _ (Pi.basisFun R ι), Matrix.toLin_eq_toLin']
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one, Matrix.of_apply]

namespace Module.Basis

/-- See also `Basis.toMatrix_reindex` which gives the `simp` normal form of this result. -/
/-
**Module.Basis.toMatrix_reindex'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_reindex' [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : 
ι' -> M) (e : ι ≃ ι') : (b.reindex e).toMatrix v = Matrix.reindexAlgEquiv R R e 
(b.toMatrix (v ∘ e))
参数：b : Basis ι R M；v : ι' -> M；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `Basis.toMatrix_reindex` which gives the `simp` normal form of this res
ult.
-/
theorem toMatrix_reindex' [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M)
    (e : ι ≃ ι') : (b.reindex e).toMatrix v =
    Matrix.reindexAlgEquiv R R e (b.toMatrix (v ∘ e)) := by
  ext
  simp [Basis.toMatrix_apply]

omit [Fintype ι'] in
@[simp]
/-
**Module.Basis.toMatrix_mulVec_repr** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_mulVec_repr [Finite ι'] (m : M) : b'.toMatrix b *ᵥ b.repr m = b'.
repr m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_mulVec_repr`：LinearMap.toMatrix_mulVec_repr (f : M₁ -
>ₗ[R] M₂) (x : M₁) : LinearMap.toMatrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMatrix_mulVec_repr [Finite ι'] (m : M) : b'.toMatrix b *ᵥ b.repr m = b'.repr m := by
  classical
  cases nonempty_fintype ι'
  simp [← LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.toMatrix_mulVec_repr]

end Module.Basis
end Fintype

namespace Module.Basis

/-- A generalization of `Basis.toMatrix_self`, in the opposite direction. -/
@[simp]
/-
**Module.Basis.toMatrix_mul_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_mul_toMatrix {ι'' : Type*} [Fintype ι'] (b'' : ι'' -> M) : b.toMa
trix b' * b'.toMatrix b'' = b.toMatrix b''
参数：b'' : ι'' -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.sum_repr_mul_repr`：sum_repr_mul_repr {ι'} [Fintype ι'] (b' 
: Basis ι' R M) (x : M) (i : ι) : (∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.
repr x i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A generalization of `Basis.toMatrix_self`, in the opposite direction.
-/
theorem toMatrix_mul_toMatrix {ι'' : Type*} [Fintype ι'] (b'' : ι'' → M) :
    b.toMatrix b' * b'.toMatrix b'' = b.toMatrix b'' := by
  have := Classical.decEq ι
  have := Classical.decEq ι'
  have := Classical.decEq ι''
  ext i j
  simp only [Matrix.mul_apply, toMatrix_apply, sum_repr_mul_repr]

/-- `b.toMatrix b'` and `b'.toMatrix b` are inverses. -/
/-
**Module.Basis.toMatrix_mul_toMatrix_flip** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basi
s`。
形式化陈述：toMatrix_mul_toMatrix_flip [DecidableEq ι] [Fintype ι'] : b.toMatrix b' * 
b'.toMatrix b = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toMatrix_mul_toMatrix`：toMatrix_mul_toMatrix {ι'' : Type*} 
[Fintype ι'] (b'' : ι'' -> M) : b.toMatrix b' * b'.toMatrix b'' = b.toMatrix b''
· 使用定理 `Module.Basis.toMatrix_self`：toMatrix_self [DecidableEq ι] : e.toMatrix e
 = 1

--- 原说明 ---
`b.toMatrix b'` and `b'.toMatrix b` are inverses.
-/
theorem toMatrix_mul_toMatrix_flip [DecidableEq ι] [Fintype ι'] :
    b.toMatrix b' * b'.toMatrix b = 1 := by rw [toMatrix_mul_toMatrix, toMatrix_self]

/-- A matrix whose columns form a basis `b'`, expressed w.r.t. a basis `b`, is invertible. -/
@[instance_reducible]
/-
**Module.Basis.invertibleToMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：invertibleToMatrix [DecidableEq ι] [Fintype ι] (b b' : Basis ι R₂ M₂) : In
vertible (b.toMatrix b')
参数：b b' : Basis ι R₂ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix whose columns form a basis `b'`, expressed w.r.t. a basis `b`, is inver
tible.
-/
def invertibleToMatrix [DecidableEq ι] [Fintype ι] (b b' : Basis ι R₂ M₂) :
    Invertible (b.toMatrix b') :=
  ⟨b'.toMatrix b, toMatrix_mul_toMatrix_flip _ _, toMatrix_mul_toMatrix_flip _ _⟩

@[simp]
/-
**Module.Basis.toMatrix_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_reindex (b : Basis ι R M) (v : ι' -> M) (e : ι ≃ ι') : (b.reindex
 e).toMatrix v = (b.toMatrix v).submatrix e.symm _root_.id
参数：b : Basis ι R M；v : ι' -> M；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_reindex (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
    (b.reindex e).toMatrix v = (b.toMatrix v).submatrix e.symm _root_.id := by
  ext
  simp only [toMatrix_apply, repr_reindex, Matrix.submatrix_apply, _root_.id,
    Finsupp.mapDomain_equiv_apply]

@[simp]
/-
**Module.Basis.toMatrix_map** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toMatrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι -> N) : (b.map f).to
Matrix v = b.toMatrix (f.symm ∘ v)
参数：b : Basis ι R M；f : M ≃ₗ[R] N；v : ι -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι → N) :
    (b.map f).toMatrix v = b.toMatrix (f.symm ∘ v) := by
  ext
  simp only [toMatrix_apply, Basis.map, LinearEquiv.trans_apply, (· ∘ ·)]
/-
**Module.Basis._root_.LinearMap.toMatrix_eq_basisToMatrix** 是 Mathlib 中的一个引理，位于命
名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.toMatrix_eq_basisToMatrix [Fintype ι] [DecidableEq ι] [Finite κ] :
    f.toMatrix b c = c.toMatrix (f ∘ b) := by ext; simp [LinearMap.toMatrix_apply, toMatrix_apply]

end Module.Basis
end MulLinearMapToMatrix

