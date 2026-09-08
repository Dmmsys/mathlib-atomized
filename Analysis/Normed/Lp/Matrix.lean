/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Determinant

/-!
# Matrices are isomorphic with linear maps between Lp spaces

This file provides a `WithLp` version of `Matrix.toLin'`.
-/

@[expose] public section

open Matrix ENNReal

variable {m n o R : Type*}

namespace Matrix
variable [Fintype n] [DecidableEq n] [CommRing R] (p q r : ℝ≥0∞)

open WithLp (toLp ofLp)

/-- `Matrix.toLin'` adapted for `PiLp R _`. -/
/-
**Matrix.toLpLin** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toLpLin : Matrix m n R ≃ₗ[R] WithLp p (n -> R) ->ₗ[R] WithLp q (m -> R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.toLin'` adapted for `PiLp R _`.
-/
def toLpLin : Matrix m n R ≃ₗ[R] WithLp p (n → R) →ₗ[R] WithLp q (m → R) :=
  toLin' ≪≫ₗ
    (WithLp.linearEquiv _ R (n → R)).symm.arrowCongr
      (WithLp.linearEquiv _ R (m → R)).symm

@[simp]
/-
**Matrix.toLpLin_toLp** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_toLp (A : Matrix m n R) (x : n -> R) : toLpLin p q A (toLp _ x) = 
toLp _ (Matrix.toLin' A x)
参数：A : Matrix m n R；x : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma toLpLin_toLp (A : Matrix m n R) (x : n → R) :
    toLpLin p q A (toLp _ x) = toLp _ (Matrix.toLin' A x) := rfl

@[simp]
/-
**Matrix.ofLp_toLpLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofLp_toLpLin (A : Matrix m n R) (x : WithLp p (n -> R)) : ofLp (toLpLin p 
q A x) = Matrix.toLin' A (ofLp x)
参数：A : Matrix m n R；x : WithLp p (n -> R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem ofLp_toLpLin (A : Matrix m n R) (x : WithLp p (n → R)) :
    ofLp (toLpLin p q A x) = Matrix.toLin' A (ofLp x) :=
  rfl
/-
**Matrix.toLpLin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_apply (M : Matrix m n R) (v : WithLp p (n -> R)) : toLpLin p q M v
 = toLp _ (M *ᵥ ofLp v)
参数：M : Matrix m n R；v : WithLp p (n -> R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toLpLin_apply (M : Matrix m n R) (v : WithLp p (n → R)) :
    toLpLin p q M v = toLp _ (M *ᵥ ofLp v) := rfl
/-
**Matrix.toLpLin_eq_toLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_eq_toLin [Finite m] : toLpLin p q = Matrix.toLin (PiLp.basisFun p 
R n) (PiLp.basisFun q R m)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toLpLin_eq_toLin [Finite m] :
    toLpLin p q = Matrix.toLin (PiLp.basisFun p R n) (PiLp.basisFun q R m) :=
  rfl

@[simp]
/-
**Matrix.toLpLin_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_one : toLpLin p p (1 : Matrix n n R) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PiLp.ext`：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp 
p α}, (∀ (i : ι), x.ofLp i = y.ofLp i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_
5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   Matrix.toLin' 1 = LinearMap.
id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toLpLin_one : toLpLin p p (1 : Matrix n n R) = LinearMap.id := by ext; simp

/-- Note that applying this theorem needs an explicit choice of `q`. -/
/-
**Matrix.toLpLin_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_mul [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o
 R) : toLpLin p r (A * B) = toLpLin q r A ∘ₗ toLpLin p q B
参数：A : Matrix m n R；B : Matrix n o R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PiLp.ext`：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp 
p α}, (∀ (i : ι), x.ofLp i = y.ofLp i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.toLin'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_
3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n]
 [inst_…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note that applying this theorem needs an explicit choice of `q`.
-/
theorem toLpLin_mul [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R) :
    toLpLin p r (A * B) = toLpLin q r A ∘ₗ toLpLin p q B := by
  ext; simp

/-- A copy of `toLpLin_mul` that works for `simp`, for the common case where the domain and codomain
have the same norm. -/
@[simp]
/-
**Matrix.toLpLin_mul_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_mul_same [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matri
x n o R) : toLpLin p p (A * B) = toLpLin p p A ∘ₗ toLpLin p p B
参数：A : Matrix m n R；B : Matrix n o R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toLpLin_mul`：toLpLin_mul [Fintype o] [DecidableEq o] (A : Matrix 
m n R) (B : Matrix n o R) : toLpLin p r (A * B) = toLpLin q r A ∘ₗ toLpLin p q B

--- 原说明 ---
A copy of `toLpLin_mul` that works for `simp`, for the common case where the dom
ain and codomain
have the same norm.
-/
theorem toLpLin_mul_same [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R) :
    toLpLin p p (A * B) = toLpLin p p A ∘ₗ toLpLin p p B :=
  toLpLin_mul _ _ _ _ _

@[simp]
/-
**Matrix.toLpLin_symm_id** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_symm_id : (toLpLin p p).symm .id = (1 : Matrix n n R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Matrix.toLpLin_one`：toLpLin_one : toLpLin p p (1 : Matrix n n R) = Linea
rMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toLpLin_symm_id : (toLpLin p p).symm .id = (1 : Matrix n n R) :=
  toLpLin p p |>.injective <| by simp

/-- Note that applying this theorem needs an explicit choice of `q`. -/
/-
**Matrix.toLpLin_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_symm_comp [Fintype o] [DecidableEq o] (A : WithLp q (n -> R) ->ₗ[R
] WithLp r (m -> R)) (B : WithLp p (o -> R) ->ₗ[R] WithLp q (n -> R)) : (toLpLin
 p r).symm (A ∘ₗ B) = (toLpLin q r).symm A * (toLpLin p q).symm B
参数：A : WithLp q (n -> R) ->ₗ[R] WithLp r (m -> R)；B : WithLp p (o -> R) ->ₗ[R] W
ithLp q (n -> R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Matrix.toLpLin_mul`：toLpLin_mul [Fintype o] [DecidableEq o] (A : Matrix 
m n R) (B : Matrix n o R) : toLpLin p r (A * B) = toLpLin q r A ∘ₗ toLpLin p q B
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note that applying this theorem needs an explicit choice of `q`.
-/
theorem toLpLin_symm_comp [Fintype o] [DecidableEq o]
    (A : WithLp q (n → R) →ₗ[R] WithLp r (m → R)) (B : WithLp p (o → R) →ₗ[R] WithLp q (n → R)) :
    (toLpLin p r).symm (A ∘ₗ B) = (toLpLin q r).symm A * (toLpLin p q).symm B :=
  toLpLin p r |>.injective <| by simp [toLpLin_mul (q := q)]

/-- `Matrix.toLinAlgEquiv'` adapted for `PiLp R _`. -/
@[simps!]
/-
**Matrix.toLpLinAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toLpLinAlgEquiv : Matrix n n R ≃ₐ[R] Module.End R (WithLp p (n -> R))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toLpLin_one`：toLpLin_one : toLpLin p p (1 : Matrix n n R) = Linea
rMap.id
· 使用定理 `Matrix.toLpLin_mul`：toLpLin_mul [Fintype o] [DecidableEq o] (A : Matrix 
m n R) (B : Matrix n o R) : toLpLin p r (A * B) = toLpLin q r A ∘ₗ toLpLin p q B

--- 原说明 ---
`Matrix.toLinAlgEquiv'` adapted for `PiLp R _`.
-/
def toLpLinAlgEquiv : Matrix n n R ≃ₐ[R] Module.End R (WithLp p (n → R)) :=
  .ofLinearEquiv (toLpLin p p) (toLpLin_one p) (toLpLin_mul p p p)

@[simp]
/-
**Matrix.toLpLin_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_pow (A : Matrix n n R) (k : Nat) : toLpLin p p (A ^ k) = toLpLin p
 p A ^ k
参数：A : Matrix n n R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem toLpLin_pow (A : Matrix n n R) (k : ℕ) : toLpLin p p (A ^ k) = toLpLin p p A ^ k :=
  map_pow (toLpLinAlgEquiv p) A k

@[simp]
/-
**Matrix.toLpLin_symm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLpLin_symm_pow (A : Module.End R (WithLp p (n -> R))) (k : Nat) : (toLpL
in p p).symm (A ^ k) = (toLpLin p p).symm A ^ k
参数：A : Module.End R (WithLp p (n -> R))；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem toLpLin_symm_pow (A : Module.End R (WithLp p (n → R))) (k : ℕ) :
    (toLpLin p p).symm (A ^ k) = (toLpLin p p).symm A ^ k :=
  map_pow (toLpLinAlgEquiv p).symm A k

end Matrix

@[simp]
/-
**LinearMap.det_toLpLin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.det_toLpLin {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing 
R] (p : Real>=0∞) (m : Matrix ι ι R) : (m.toLpLin p p).det = m.det
参数：p : Real>=0∞；m : Matrix ι ι R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_toLin`：det_toLin (b : Basis ι R M) (f : Matrix ι ι R) : Li
nearMap.det (Matrix.toLin b b f) = f.det
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.det_toLpLin {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (p : ℝ≥0∞)
    (m : Matrix ι ι R) : (m.toLpLin p p).det = m.det := by
  simp [Matrix.toLpLin_eq_toLin]
