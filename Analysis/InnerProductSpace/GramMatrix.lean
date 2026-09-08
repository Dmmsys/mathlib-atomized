/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semidefiniteness.
Results require `RCLike 𝕜`.

## Main definition

* `Matrix.gram` : the `Matrix n n 𝕜` with `⟪v i, v j⟫` at `i j : n`, where `v : n → E` for an
  `Inner 𝕜 E`.

## Main results

* `Matrix.posSemidef_gram`: Gram matrices are positive semidefinite.
* `Matrix.posDef_gram_iff_linearIndependent`: Linear independence of `v` is
  equivalent to positive definiteness of `gram 𝕜 v`.
-/

@[expose] public section

open RCLike Real Matrix

open scoped InnerProductSpace ComplexOrder ComplexConjugate

variable {E n α 𝕜 : Type*}
namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
/-
**Matrix.gram** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：gram (𝕜 : Type*) [Inner 𝕜 E] (v : n -> E) : Matrix n n 𝕜
参数：𝕜 : Type*；v : n -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entries of a Gram matrix are inner products of vectors in an inner product s
pace.
-/
def gram (𝕜 : Type*) [Inner 𝕜 E] (v : n → E) : Matrix n n 𝕜 := of fun i j ↦ ⟪v i, v j⟫_𝕜

@[simp]
/-
**Matrix.gram_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：gram_apply [Inner 𝕜 E] (v : n -> E) (i j : n) : (gram 𝕜 v) i j = ⟪v i, v j
⟫_𝕜
参数：v : n -> E；i j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma gram_apply [Inner 𝕜 E] (v : n → E) (i j : n) :
    (gram 𝕜 v) i j = ⟪v i, v j⟫_𝕜 := rfl

variable [RCLike 𝕜]

section SemiInnerProductSpace
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

@[simp]
/-
**Matrix.gram_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：gram_zero : gram 𝕜 (0 : n -> E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
-/
lemma gram_zero : gram 𝕜 (0 : n → E) = 0 := Matrix.ext fun _ _ ↦ inner_zero_left _

@[simp]
/-
**Matrix.gram_single** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：gram_single [DecidableEq n] (i : n) (x : E) : gram 𝕜 (Pi.single i x) = Mat
rix.single i i ⟪x, x⟫_𝕜
参数：i : n；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `Matrix.single.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type u_7}
 {inst : DecidableEq m} [inst_1 : DecidableEq m] {inst_2 : DecidableEq n}   [ins
t_3 : Decidabl…
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
-/
lemma gram_single [DecidableEq n] (i : n) (x : E) :
    gram 𝕜 (Pi.single i x) = Matrix.single i i ⟪x, x⟫_𝕜 := by
  ext j k
  obtain hij | rfl := ne_or_eq i j
  · simp [hij]
  obtain hik | rfl := ne_or_eq i k
  · simp [hik]
  simp
/-
**Matrix.submatrix_gram** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：submatrix_gram (v : n -> E) {m : Set n} (f : m -> n) : (gram 𝕜 v).submatri
x f f = gram 𝕜 (v ∘ f)
参数：v : n -> E；f : m -> n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma submatrix_gram (v : n → E) {m : Set n} (f : m → n) :
    (gram 𝕜 v).submatrix f f = gram 𝕜 (v ∘ f) := rfl

variable (𝕜) in
/-- A Gram matrix is Hermitian. -/
/-
**Matrix.isHermitian_gram** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_gram (v : n -> E) : (gram 𝕜 v).IsHermitian
参数：v : n -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫

--- 原说明 ---
A Gram matrix is Hermitian.
-/
lemma isHermitian_gram (v : n → E) : (gram 𝕜 v).IsHermitian :=
  Matrix.ext fun _ _ ↦ inner_conj_symm _ _
/-
**Matrix.star_dotProduct_gram_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_dotProduct_gram_mulVec [Fintype n] (v : n -> E) (x y : n -> 𝕜) : star
 x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑ i, y i • v i⟫_𝕜
参数：v : n -> E；x y : n -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
-/
theorem star_dotProduct_gram_mulVec [Fintype n] (v : n → E) (x y : n → 𝕜) :
    star x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑ i, y i • v i⟫_𝕜 := by
  trans ∑ i, ∑ j, conj (x i) * y j * ⟪v i, v j⟫_𝕜
  · simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def,
      gram_apply, Pi.star_apply]
  · simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]

variable [Finite n]

variable (𝕜) in
/-- A Gram matrix is positive semidefinite. -/
/-
**Matrix.posSemidef_gram** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posSemidef_gram (v : n -> E) : PosSemidef (gram 𝕜 v)
参数：v : n -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`：of_dotProduct_mulVec_nonn
eg {M : Matrix n n R} (hM1 : M.IsHermitian) (hM2 : forall x, 0 <= star x ⬝ᵥ (M *
ᵥ x)) : M.PosSemidef
· 使用引理 `Matrix.isHermitian_gram`：isHermitian_gram (v : n -> E) : (gram 𝕜 v).IsHe
rmitian
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.star_dotProduct_gram_mulVec`：star_dotProduct_gram_mulVec [Fintype
 n] (v : n -> E) (x y : n -> 𝕜) : star x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑
 i, y i • v i⟫_𝕜
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `RCLike.re_ofReal_pow`：re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^
 n) = a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `RCLike.im_ofReal_pow`：im_ofReal_pow (a : Real) (n : Nat) : im ((a : K) ^
 n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
A Gram matrix is positive semidefinite.
-/
theorem posSemidef_gram (v : n → E) :
    PosSemidef (gram 𝕜 v) := by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_gram _ _) fun x ↦ ?_
  rw [star_dotProduct_gram_mulVec, le_iff_re_im]
  simp

/-- In a normed space, positive definiteness of `gram 𝕜 v` implies linear independence of `v`. -/
/-
**Matrix.linearIndependent_of_posDef_gram** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linearIndependent_of_posDef_gram {v : n -> E} (h_gram : PosDef (gram 𝕜 v))
 : LinearIndependent 𝕜 v
参数：h_gram : PosDef (gram 𝕜 v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用引理 `Matrix.PosDef.dotProduct_mulVec_pos`：dotProduct_mulVec_pos {M : Matrix n
 n R} (hM : M.PosDef) {x} (hx : x != 0) : 0 < star x ⬝ᵥ (M *ᵥ x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matrix.star_dotProduct_gram_mulVec`：star_dotProduct_gram_mulVec [Fintype
 n] (v : n -> E) (x y : n -> 𝕜) : star x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑
 i, y i • v i⟫_𝕜
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
In a normed space, positive definiteness of `gram 𝕜 v` implies linear independen
ce of `v`.
-/
theorem linearIndependent_of_posDef_gram {v : n → E} (h_gram : PosDef (gram 𝕜 v)) :
    LinearIndependent 𝕜 v := by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff]
  intro y hy
  have := h_gram.dotProduct_mulVec_pos (x := y)
  simp_all [star_dotProduct_gram_mulVec]

omit [Finite n] in
/-
**Matrix.linearIndependent_of_det_gram_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：linearIndependent_of_det_gram_ne_zero [Fintype n] [DecidableEq n] {v : n -
> E} (h : (gram 𝕜 v).det != 0) : LinearIndependent 𝕜 v
参数：h : (gram 𝕜 v).det != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.linearIndependent_of_posDef_gram`：linearIndependent_of_posDef_gra
m {v : n -> E} (h_gram : PosDef (gram 𝕜 v)) : LinearIndependent 𝕜 v
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.PosSemidef.posDef_iff_det_ne_zero`：∀ {𝕜 : Type u_1} {n : Type u_2
} [inst : RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n 
n 𝕜},   A.PosSemidef → (A.PosD…
· 使用定理 `Matrix.posSemidef_gram`：posSemidef_gram (v : n -> E) : PosSemidef (gram 
𝕜 v)
-/
theorem linearIndependent_of_det_gram_ne_zero [Fintype n] [DecidableEq n] {v : n → E}
    (h : (gram 𝕜 v).det ≠ 0) : LinearIndependent 𝕜 v :=
  linearIndependent_of_posDef_gram <| (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero.mpr h

end SemiInnerProductSpace

section NormedInnerProductSpace
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Finite n]

/-- In a normed space, linear independence of `v` implies positive definiteness of `gram 𝕜 v`. -/
/-
**Matrix.posDef_gram_of_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posDef_gram_of_linearIndependent {v : n -> E} (h_li : LinearIndependent 𝕜 
v) : PosDef (gram 𝕜 v)
参数：h_li : LinearIndependent 𝕜 v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosDef.of_dotProduct_mulVec_pos`：of_dotProduct_mulVec_pos {M : Ma
trix n n R} (hM1 : M.IsHermitian) (hM2 : forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M 
*ᵥ x)) : M.PosDef
· 使用引理 `Matrix.isHermitian_gram`：isHermitian_gram (v : n -> E) : (gram 𝕜 v).IsHe
rmitian
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Matrix.PosSemidef.dotProduct_mulVec_nonneg`：dotProduct_mulVec_nonneg {M 
: Matrix n n R} (hM : M.PosSemidef) : forall x : n -> R, 0 <= star x ⬝ᵥ (M *ᵥ x)
· 使用定理 `Matrix.posSemidef_gram`：posSemidef_gram (v : n -> E) : PosSemidef (gram 
𝕜 v)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.star_dotProduct_gram_mulVec`：star_dotProduct_gram_mulVec [Fintype
 n] (v : n -> E) (x y : n -> 𝕜) : star x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑
 i, y i • v i⟫_𝕜
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
In a normed space, linear independence of `v` implies positive definiteness of `
gram 𝕜 v`.
-/
theorem posDef_gram_of_linearIndependent
    {v : n → E} (h_li : LinearIndependent 𝕜 v) : PosDef (gram 𝕜 v) := by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff] at h_li
  refine .of_dotProduct_mulVec_pos (isHermitian_gram _ _) fun x hx ↦
    ((posSemidef_gram ..).dotProduct_mulVec_nonneg _).lt_of_ne' ?_
  rw [star_dotProduct_gram_mulVec, inner_self_eq_zero.ne]
  exact mt (h_li x) (mt funext hx)

/-- In a normed space, linear independence of `v` is equivalent to positive definiteness of
`gram 𝕜 v`. -/
/-
**Matrix.posDef_gram_iff_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posDef_gram_iff_linearIndependent {v : n -> E} : PosDef (gram 𝕜 v) ↔ Linea
rIndependent 𝕜 v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.linearIndependent_of_posDef_gram`：linearIndependent_of_posDef_gra
m {v : n -> E} (h_gram : PosDef (gram 𝕜 v)) : LinearIndependent 𝕜 v
· 使用定理 `Matrix.posDef_gram_of_linearIndependent`：posDef_gram_of_linearIndependen
t {v : n -> E} (h_li : LinearIndependent 𝕜 v) : PosDef (gram 𝕜 v)

--- 原说明 ---
In a normed space, linear independence of `v` is equivalent to positive definite
ness of
`gram 𝕜 v`.
-/
theorem posDef_gram_iff_linearIndependent {v : n → E} :
    PosDef (gram 𝕜 v) ↔ LinearIndependent 𝕜 v :=
  ⟨linearIndependent_of_posDef_gram, posDef_gram_of_linearIndependent⟩

omit [Finite n] in
/-
**Matrix.det_gram_ne_zero_iff_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x`。
形式化陈述：det_gram_ne_zero_iff_linearIndependent [Fintype n] [DecidableEq n] {v : n 
-> E} : (gram 𝕜 v).det != 0 ↔ LinearIndependent 𝕜 v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.posDef_gram_iff_linearIndependent`：posDef_gram_iff_linearIndepend
ent {v : n -> E} : PosDef (gram 𝕜 v) ↔ LinearIndependent 𝕜 v
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.PosSemidef.posDef_iff_det_ne_zero`：∀ {𝕜 : Type u_1} {n : Type u_2
} [inst : RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n 
n 𝕜},   A.PosSemidef → (A.PosD…
· 使用定理 `Matrix.posSemidef_gram`：posSemidef_gram (v : n -> E) : PosSemidef (gram 
𝕜 v)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem det_gram_ne_zero_iff_linearIndependent [Fintype n] [DecidableEq n] {v : n → E} :
    (gram 𝕜 v).det ≠ 0 ↔ LinearIndependent 𝕜 v := by
  rw [← posDef_gram_iff_linearIndependent, (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero]

omit [Finite n] in
/-
**Matrix.gram_eq_conjTranspose_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：gram_eq_conjTranspose_mul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 
𝕜 E) (v : n -> E) : letI m
参数：b : OrthonormalBasis ι 𝕜 E；v : n -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `OrthonormalBasis.sum_inner_mul_inner`：∀ {ι : Type u_1} {𝕜 : Type u_3} [i
nst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Inner
ProductSpace 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gram_eq_conjTranspose_mul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (v : n → E) :
    letI m := of fun i j ↦ b.repr (v j) i
    gram 𝕜 v = mᴴ * m := by
  ext i j
  simp [mul_apply, b.repr_apply_apply, b.sum_inner_mul_inner]

omit [Finite n] in
@[simp]
/-
**Matrix.gram_eq_one_iff_orthonormal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：gram_eq_one_iff_orthonormal [DecidableEq n] {v : n -> E} : gram 𝕜 v = 1 ↔ 
Orthonormal 𝕜 v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma gram_eq_one_iff_orthonormal [DecidableEq n] {v : n → E} : gram 𝕜 v = 1 ↔ Orthonormal 𝕜 v := by
  simp [← Matrix.ext_iff, orthonormal_iff_ite, Matrix.one_apply]

omit [Finite n] in
/-- Inequality `‖f x‖ ≤ ‖f‖ * ‖x‖` lifted to Gram matrices. -/
/-
**Matrix.posSemidef_opNorm_smul_gram_sub_gram** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：posSemidef_opNorm_smul_gram_sub_gram {F} [NormedAddCommGroup F] [InnerProd
uctSpace 𝕜 F] (v : n -> E) (f : E ->L[𝕜] F) : (‖f‖ ^ 2 • gram 𝕜 v - gram 𝕜 (f ∘ 
v)).PosSemidef
参数：v : n -> E；f : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.sub`：∀ {α : Type u_1} {n : Type u_4} [inst : AddGroup
 α] [inst_1 : StarAddMonoid α] {A B : Matrix n n α},   A.IsHermitian → B.IsHermi
tian → (A - …
· 使用定理 `Matrix.IsHermitian.smul`：∀ {α : Type u_1} {n : Type u_4} {R : Type u_5} 
[inst : Star R] [inst_1 : Star α] [inst_2 : SMul R α] [StarModule R α]   {A : Ma
trix n n α}, …
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用引理 `Matrix.isHermitian_gram`：isHermitian_gram (v : n -> E) : (gram 𝕜 v).IsHe
rmitian
· 使用定理 `IsSelfAdjoint.pow`：pow {x : R} (hx : IsSelfAdjoint x) (n : Nat) : IsSelf
Adjoint (x ^ n)
· 使用定理 `IsSelfAdjoint.apply`：∀ {ι : Type u_3} {α : ι → Type u_4} [inst : (i : ι)
 → Star (α i)] {f : (i : ι) → α i},   IsSelfAdjoint f → ∀ (i : ι), IsSelfAdjoint
 (f i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.isSelfAdjoint`：∀ {ι : Type u_3} {α : ι → Type u_4} [inst : (i : ι) → 
Star (α i)] {f : (i : ι) → α i},   IsSelfAdjoint f ↔ ∀ (i : ι), IsSelfAdjoint (f
 i)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Inequality `‖f x‖ ≤ ‖f‖ * ‖x‖` lifted to Gram matrices.
-/
theorem posSemidef_opNorm_smul_gram_sub_gram {F} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (v : n → E) (f : E →L[𝕜] F) : (‖f‖ ^ 2 • gram 𝕜 v - gram 𝕜 (f ∘ v)).PosSemidef := by
  refine ⟨(isHermitian_gram 𝕜 v).smul (((Pi.isSelfAdjoint.mpr (congrFun rfl)).apply f).pow 2)
    |>.sub (isHermitian_gram 𝕜 (f ∘ v)), fun c ↦ ?_⟩
  simp_rw [Finsupp.sum, Matrix.sub_apply, Matrix.smul_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, sub_nonneg]
  calc
    ∑ x ∈ c.support, ∑ y ∈ c.support, star (c x) * gram 𝕜 (f ∘ v) x y * c y
    _ = (‖f (∑ x ∈ c.support, c x • v x)‖ : 𝕜) ^ 2 := ?h1
    _ ≤ ‖f‖ ^ 2 • (‖∑ i ∈ c.support, c i • v i‖ : 𝕜) ^ 2 := by
      norm_cast
      grw [f.le_opNorm _, smul_eq_mul, ← mul_pow]
    _ = ∑ x ∈ c.support, ∑ y ∈ c.support, star (c x) * ‖f‖ ^ 2 • gram 𝕜 v x y * c y := ?h2
  all_goals
    rw [Finset.sum_comm]
    simp [← inner_self_eq_norm_sq_to_K, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
      Finset.mul_sum, Finset.smul_sum, RCLike.real_smul_eq_coe_mul]
    grind

end NormedInnerProductSpace

end Matrix

