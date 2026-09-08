/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `Matrix.Nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/

@[expose] public section


namespace Matrix

section Finite

variable {m n R A : Type*} [NonUnitalNonAssocSemiring R] [Finite m] [Finite n] (M : Matrix m n R)

attribute [local instance] Fintype.ofFinite

/-- A matrix `M` is right-separating if for all `w ≠ 0`, there is a `v` with `v * M * w ≠ 0`. -/
/-
**Matrix.SeparatingRight** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：SeparatingRight : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix `M` is right-separating if for all `w ≠ 0`, there is a `v` with `v * M 
* w ≠ 0`.
-/
def SeparatingRight : Prop :=
  (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0)

/-- A matrix `M` is right-separating if for all `v ≠ 0`, there is a `w` with `v * M * w ≠ 0`. -/
/-
**Matrix.SeparatingLeft** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：SeparatingLeft : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix `M` is right-separating if for all `v ≠ 0`, there is a `w` with `v * M 
* w ≠ 0`.
-/
def SeparatingLeft : Prop :=
  (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0)

/-- A matrix `M` is nondegenerate if it is both left-separating and right-separating.

See also `Matrix.Nonsingular`. -/
@[mk_iff]
/-
**Matrix.Nondegenerate** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_1} →   {n : Type u_2} → {R : Type u_3} → [NonUnitalNonAssocSem
iring R] → [Finite m] → [Finite n] → Matrix m n R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix `M` is nondegenerate if it is both left-separating and right-separating
.

See also `Matrix.Nonsingular`.
-/
structure Nondegenerate (M : Matrix m n R) : Prop where
  separatingLeft : SeparatingLeft M
  separatingRight : SeparatingRight M

end Finite

section CommSemiring

variable {m n R : Type*} [CommSemiring R] {M : Matrix m n R}

/-
**Matrix.separatingRight_def** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：separatingRight_def [Fintype m] [Fintype n] : M.SeparatingRight ↔ (forall 
w, (forall v, v ⬝ᵥ M *ᵥ w = 0) -> w = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
-/
lemma separatingRight_def [Fintype m] [Fintype n] :
    M.SeparatingRight ↔ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  refine forall_congr' fun w ↦ ⟨fun hM hw ↦ hM ?_, fun hM hw ↦ hM ?_⟩ <;>
  convert! hw
/-
**Matrix.separatingLeft_def** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：separatingLeft_def [Fintype m] [Fintype n] : M.SeparatingLeft ↔ (forall v,
 (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
-/
lemma separatingLeft_def [Fintype m] [Fintype n] :
    M.SeparatingLeft ↔ (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) := by
  refine forall_congr' fun v ↦ ⟨fun hM hv ↦ hM ?_, fun hM hv ↦ hM ?_⟩ <;>
  convert! hv
/-
**Matrix.nondegenerate_def** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nondegenerate_def [Fintype m] [Fintype n] : M.Nondegenerate ↔ (forall v, (
forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0) ∧ (forall w, (forall v, v ⬝ᵥ M *ᵥ w = 0) ->
 w = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nondegenerate_iff`：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3}
 [inst : NonUnitalNonAssocSemiring R] [inst_1 : Finite m]   [inst_2 : Finite n] 
(M : Matrix m …
· 使用引理 `Matrix.separatingLeft_def`：separatingLeft_def [Fintype m] [Fintype n] : 
M.SeparatingLeft ↔ (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0)
· 使用引理 `Matrix.separatingRight_def`：separatingRight_def [Fintype m] [Fintype n] 
: M.SeparatingRight ↔ (forall w, (forall v, v ⬝ᵥ M *ᵥ w = 0) -> w = 0)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nondegenerate_def [Fintype m] [Fintype n] :
    M.Nondegenerate ↔
      (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) ∧ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  rw [nondegenerate_iff, separatingLeft_def, separatingRight_def]
/-
**Matrix.separatingLeft_iff_forall_vecMul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mat
rix`。
形式化陈述：separatingLeft_iff_forall_vecMul_eq_zero [Fintype m] [Finite n] : M.Separa
tingLeft ↔ forall v, v ᵥ* M = 0 -> v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.separatingLeft_def`：separatingLeft_def [Fintype m] [Fintype n] : 
M.SeparatingLeft ↔ (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem separatingLeft_iff_forall_vecMul_eq_zero [Fintype m] [Finite n] :
    M.SeparatingLeft ↔ ∀ v, v ᵥ* M = 0 → v = 0 := by
  have := Fintype.ofFinite n
  rw [separatingLeft_def]
  refine ⟨fun h v hv ↦ h v fun w ↦ ?_, fun h w hw ↦ h w <| funext fun i ↦ ?_⟩
  · simp [dotProduct_mulVec, hv]
  · classical simpa using! hw <| Pi.single i 1
/-
**Matrix.separatingRight_iff_forall_mulVec_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
形式化陈述：separatingRight_iff_forall_mulVec_eq_zero [Finite m] [Fintype n] : M.Separ
atingRight ↔ forall v, M *ᵥ v = 0 -> v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.separatingRight_def`：separatingRight_def [Fintype m] [Fintype n] 
: M.SeparatingRight ↔ (forall w, (forall v, v ⬝ᵥ M *ᵥ w = 0) -> w = 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `single_dotProduct`：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ 
v = x * v i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem separatingRight_iff_forall_mulVec_eq_zero [Finite m] [Fintype n] :
    M.SeparatingRight ↔ ∀ v, M *ᵥ v = 0 → v = 0 := by
  have := Fintype.ofFinite m
  rw [separatingRight_def]
  refine ⟨fun h v hv ↦ h v fun w ↦ ?_, fun h w hw ↦ h w <| funext fun i ↦ ?_⟩
  · simp [hv]
  · classical simpa using hw <| Pi.single i 1
/-
**Matrix.SeparatingLeft.eq_zero_of_vecMul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mat
rix.SeparatingLeft`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : CommSemiring R] {M 
: Matrix m n R} [inst_1 : Fintype m]   [inst_2 : Finite n], M.SeparatingLeft → ∀
 {v : m → R}, Matrix.vecMul v M = 0 → v = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.separatingLeft_iff_forall_vecMul_eq_zero`：separatingLeft_iff_fora
ll_vecMul_eq_zero [Fintype m] [Finite n] : M.SeparatingLeft ↔ forall v, v ᵥ* M =
 0 -> v = 0
-/
theorem SeparatingLeft.eq_zero_of_vecMul_eq_zero [Fintype m] [Finite n] (hM : M.SeparatingLeft)
    {v : m → R} (hv : v ᵥ* M = 0) : v = 0 :=
  separatingLeft_iff_forall_vecMul_eq_zero.mp hM v hv
/-
**Matrix.SeparatingRight.eq_zero_of_mulVec_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix.SeparatingRight`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : CommSemiring R] {M 
: Matrix m n R} [inst_1 : Finite m]   [inst_2 : Fintype n], M.SeparatingRight → 
∀ {v : n → R}, M.mulVec v = 0 → v = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.separatingRight_iff_forall_mulVec_eq_zero`：separatingRight_iff_fo
rall_mulVec_eq_zero [Finite m] [Fintype n] : M.SeparatingRight ↔ forall v, M *ᵥ 
v = 0 -> v = 0
-/
theorem SeparatingRight.eq_zero_of_mulVec_eq_zero [Finite m] [Fintype n] (hM : M.SeparatingRight)
    {v : n → R} (hv : M *ᵥ v = 0) : v = 0 :=
  separatingRight_iff_forall_mulVec_eq_zero.mp hM v hv
/-
**Matrix.nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `Matrix`。
形式化陈述：nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero [Fintype m] [Fintype n]
 : M.Nondegenerate ↔ (forall v, v ᵥ* M = 0 -> v = 0) ∧ (forall v, M *ᵥ v = 0 -> 
v = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nondegenerate_iff`：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3}
 [inst : NonUnitalNonAssocSemiring R] [inst_1 : Finite m]   [inst_2 : Finite n] 
(M : Matrix m …
· 使用定理 `Matrix.separatingLeft_iff_forall_vecMul_eq_zero`：separatingLeft_iff_fora
ll_vecMul_eq_zero [Fintype m] [Finite n] : M.SeparatingLeft ↔ forall v, v ᵥ* M =
 0 -> v = 0
· 使用定理 `Matrix.separatingRight_iff_forall_mulVec_eq_zero`：separatingRight_iff_fo
rall_mulVec_eq_zero [Finite m] [Fintype n] : M.SeparatingRight ↔ forall v, M *ᵥ 
v = 0 -> v = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero [Fintype m] [Fintype n] :
    M.Nondegenerate ↔ (∀ v, v ᵥ* M = 0 → v = 0) ∧ (∀ v, M *ᵥ v = 0 → v = 0) := by
  rw [nondegenerate_iff, separatingLeft_iff_forall_vecMul_eq_zero,
    separatingRight_iff_forall_mulVec_eq_zero]

@[simp]
/-
**Matrix.separatingLeft_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：separatingLeft_transpose_iff [Finite m] [Finite n] : Mᵀ.SeparatingLeft ↔ M
.SeparatingRight
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matrix.dotProduct_transpose_mulVec`：dotProduct_transpose_mulVec [Fintype
 m] [Fintype n] (A : Matrix m n α) (x : n -> α) (y : m -> α) : x ⬝ᵥ Aᵀ *ᵥ y = y 
⬝ᵥ A *ᵥ x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem separatingLeft_transpose_iff [Finite m] [Finite n] :
    Mᵀ.SeparatingLeft ↔ M.SeparatingRight := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingLeft_def, separatingRight_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingRight.separatingLeft_transpose⟩ := separatingLeft_transpose_iff

@[simp]
/-
**Matrix.separatingRight_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：separatingRight_transpose_iff [Finite m] [Finite n] : Mᵀ.SeparatingRight ↔
 M.SeparatingLeft
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matrix.dotProduct_transpose_mulVec`：dotProduct_transpose_mulVec [Fintype
 m] [Fintype n] (A : Matrix m n α) (x : n -> α) (y : m -> α) : x ⬝ᵥ Aᵀ *ᵥ y = y 
⬝ᵥ A *ᵥ x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem separatingRight_transpose_iff [Finite m] [Finite n] :
    Mᵀ.SeparatingRight ↔ M.SeparatingLeft := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingRight_def, separatingLeft_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingLeft.separatingRight_transpose⟩ := separatingRight_transpose_iff

@[simp]
/-
**Matrix.nondegenerate_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nondegenerate_transpose_iff [Finite m] [Finite n] : Mᵀ.Nondegenerate ↔ M.N
ondegenerate
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
theorem nondegenerate_transpose_iff [Finite m] [Finite n] : Mᵀ.Nondegenerate ↔ M.Nondegenerate := by
  simp [nondegenerate_iff, and_comm]

alias ⟨_, Nondegenerate.transpose⟩ := nondegenerate_transpose_iff

variable [Fintype m] [Fintype n]

/-- If `M` is nondegenerate and `w * M * v = 0` for all `w`, then `v = 0`. -/
/-
**Matrix.Nondegenerate.eq_zero_of_ortho** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nondeg
enerate`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : CommSemiring R] {M 
: Matrix m n R} [inst_1 : Fintype m]   [inst_2 : Fintype n], M.Nondegenerate → ∀
 {v : m → R}, (∀ (w : n → R), v ⬝ᵥ M.mulVec w = 0) → v = 0
参数：∀ (w : n → R), v ⬝ᵥ M.mulVec w = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.nondegenerate_def`：nondegenerate_def [Fintype m] [Fintype n] : M.
Nondegenerate ↔ (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0) ∧ (forall w, (f
orall v, v ⬝ᵥ …

--- 原说明 ---
If `M` is nondegenerate and `w * M * v = 0` for all `w`, then `v = 0`.
-/
theorem Nondegenerate.eq_zero_of_ortho (hM : Nondegenerate M) {v : m → R}
    (hv : ∀ w, v ⬝ᵥ M *ᵥ w = 0) : v = 0 :=
  (nondegenerate_def.mp hM).1 v hv

/-- If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w * M * v ≠ 0`. -/
/-
**Matrix.Nondegenerate.exists_not_ortho_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix.Nondegenerate`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : CommSemiring R] {M 
: Matrix m n R} [inst_1 : Fintype m]   [inst_2 : Fintype n], M.Nondegenerate → ∀
 {v : m → R}, v ≠ 0 → ∃ w, v ⬝ᵥ M.mulVec w ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Matrix.Nondegenerate.eq_zero_of_ortho`：∀ {m : Type u_1} {n : Type u_2} {
R : Type u_3} [inst : CommSemiring R] {M : Matrix m n R} [inst_1 : Fintype m]   
[inst_2 : Fintype n], M.Non…

--- 原说明 ---
If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w * M * v
 ≠ 0`.
-/
theorem Nondegenerate.exists_not_ortho_of_ne_zero (hM : Nondegenerate M)
    {v : m → R} (hv : v ≠ 0) : ∃ w, v ⬝ᵥ M *ᵥ w ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)

/-- If `M` is nondegenerate and `w * M * v = 0` for all `v`, then `w = 0`. -/
/-
**Matrix.Nondegenerate.eq_zero_of_ortho'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nonde
generate`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : CommSemiring R] {M 
: Matrix m n R} [inst_1 : Fintype m]   [inst_2 : Fintype n], M.Nondegenerate → ∀
 {w : n → R}, (∀ (v : m → R), v ⬝ᵥ M.mulVec w = 0) → w = 0
参数：∀ (v : m → R), v ⬝ᵥ M.mulVec w = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.nondegenerate_def`：nondegenerate_def [Fintype m] [Fintype n] : M.
Nondegenerate ↔ (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0) ∧ (forall w, (f
orall v, v ⬝ᵥ …

--- 原说明 ---
If `M` is nondegenerate and `w * M * v = 0` for all `v`, then `w = 0`.
-/
theorem Nondegenerate.eq_zero_of_ortho' (hM : Nondegenerate M) {w : n → R}
    (hw : ∀ v, v ⬝ᵥ M *ᵥ w = 0) : w = 0 :=
  (nondegenerate_def.mp hM).2 w hw

/-- If `M` is nondegenerate and `w ≠ 0`, then there is some `v` such that `v * M * w ≠ 0`. -/
/-
**Matrix.Nondegenerate.exists_not_ortho_of_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `M
atrix.Nondegenerate`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : CommSemiring R] {M 
: Matrix m n R} [inst_1 : Fintype m]   [inst_2 : Fintype n], M.Nondegenerate → ∀
 {w : n → R}, w ≠ 0 → ∃ v, v ⬝ᵥ M.mulVec w ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Matrix.Nondegenerate.eq_zero_of_ortho'`：∀ {m : Type u_1} {n : Type u_2} 
{R : Type u_3} [inst : CommSemiring R] {M : Matrix m n R} [inst_1 : Fintype m]  
 [inst_2 : Fintype n], M.Non…

--- 原说明 ---
If `M` is nondegenerate and `w ≠ 0`, then there is some `v` such that `v * M * w
 ≠ 0`.
-/
theorem Nondegenerate.exists_not_ortho_of_ne_zero' (hM : Nondegenerate M) {w : n → R} (hw : w ≠ 0) :
    ∃ v, v ⬝ᵥ M *ᵥ w ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho' hw)

end CommSemiring

section Determinant
variable {m R : Type*} [CommRing R] [Fintype m] [DecidableEq m] {M : Matrix m m R}

open scoped nonZeroDivisors

/-
**Matrix.SeparatingLeft.of_det_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem SeparatingLeft.of_det_mem_nonZeroDivisors (hM : M.det ∈ R⁰) : M.SeparatingLeft := by
  refine separatingLeft_def.mpr fun v h ↦ funext fun i ↦ mem_nonZeroDivisors_iff_left.mp hM _ ?_
  simpa using h <| M.cramer <| Pi.single i 1
/-
**Matrix.Nondegenerate.of_det_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Mat
rix.Nondegenerate`。
形式化陈述：∀ {m : Type u_1} {R : Type u_2} [inst : CommRing R] [inst_1 : Fintype m] [
inst_2 : DecidableEq m] {M : Matrix m m R},   M.det ∈ nonZeroDivisors R → M.Nond
egenerate
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Nondegenerate.0.Matrix.SeparatingL
eft.of_det_mem_nonZeroDivisors`：∀ {m : Type u_1} {R : Type u_2} [inst : CommRing
 R] [inst_1 : Fintype m] [inst_2 : DecidableEq m] {M : Matrix m m R},   M.det ∈ 
nonZeroDivis…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.separatingLeft_transpose_iff`：separatingLeft_transpose_iff [Finit
e m] [Finite n] : Mᵀ.SeparatingLeft ↔ M.SeparatingRight
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
-/
theorem Nondegenerate.of_det_mem_nonZeroDivisors (hM : M.det ∈ R⁰) : M.Nondegenerate where
  separatingLeft := .of_det_mem_nonZeroDivisors hM
  separatingRight := separatingLeft_transpose_iff.mp <| .of_det_mem_nonZeroDivisors <| by simpa

/-- If `M` is square and has nonzero determinant, then `M` as a bilinear form on `n → R` is
nondegenerate. The "iff" implication, `nondegenerate_iff_det_ne_zero`, is proved in a later file.

See also `BilinForm.nondegenerateOfDetNeZero'` and `BilinForm.nondegenerateOfDetNeZero`.
-/
/-
**Matrix.nondegenerate_of_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nondegenerate_of_det_ne_zero [NoZeroDivisors R] (hM : M.det != 0) : M.Nond
egenerate
参数：hM : M.det != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Nondegenerate.of_det_mem_nonZeroDivisors`：∀ {m : Type u_1} {R : T
ype u_2} [inst : CommRing R] [inst_1 : Fintype m] [inst_2 : DecidableEq m] {M : 
Matrix m m R},   M.det ∈ nonZeroDivis…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰

--- 原说明 ---
If `M` is square and has nonzero determinant, then `M` as a bilinear form on `n 
→ R` is
nondegenerate. The "iff" implication, `nondegenerate_iff_det_ne_zero`, is proved
 in a later file.

See also `BilinForm.nondegenerateOfDetNeZero'` and `BilinForm.nondegenerateOfDet
NeZero`.
-/
theorem nondegenerate_of_det_ne_zero [NoZeroDivisors R] (hM : M.det ≠ 0) : M.Nondegenerate :=
  .of_det_mem_nonZeroDivisors <| mem_nonZeroDivisors_of_ne_zero hM
/-
**Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `Matrix`。
形式化陈述：eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero (hM : M.det in R⁰) {v
 : m -> R} (hv : v ᵥ* M = 0) : v = 0
参数：hM : M.det in R⁰；hv : v ᵥ* M = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SeparatingLeft.eq_zero_of_vecMul_eq_zero`：∀ {m : Type u_1} {n : T
ype u_2} {R : Type u_3} [inst : CommSemiring R] {M : Matrix m n R} [inst_1 : Fin
type m]   [inst_2 : Finite n], M.Sepa…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.Nondegenerate.separatingLeft`：∀ {m : Type u_1} {n : Type u_2} {R 
: Type u_3} [inst : NonUnitalNonAssocSemiring R] [inst_1 : Finite m]   [inst_2 :
 Finite n] {M : Matrix m …
· 使用定理 `Matrix.Nondegenerate.of_det_mem_nonZeroDivisors`：∀ {m : Type u_1} {R : T
ype u_2} [inst : CommRing R] [inst_1 : Fintype m] [inst_2 : DecidableEq m] {M : 
Matrix m m R},   M.det ∈ nonZeroDivis…
-/
theorem eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero (hM : M.det ∈ R⁰)
    {v : m → R} (hv : v ᵥ* M = 0) : v = 0 :=
  Nondegenerate.of_det_mem_nonZeroDivisors hM |>.separatingLeft.eq_zero_of_vecMul_eq_zero hv
/-
**Matrix.eq_zero_of_vecMul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eq_zero_of_vecMul_eq_zero [NoZeroDivisors R] (hM : M.det != 0) {v : m -> R
} (hv : v ᵥ* M = 0) : v = 0
参数：hM : M.det != 0；hv : v ᵥ* M = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SeparatingLeft.eq_zero_of_vecMul_eq_zero`：∀ {m : Type u_1} {n : T
ype u_2} {R : Type u_3} [inst : CommSemiring R] {M : Matrix m n R} [inst_1 : Fin
type m]   [inst_2 : Finite n], M.Sepa…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.Nondegenerate.separatingLeft`：∀ {m : Type u_1} {n : Type u_2} {R 
: Type u_3} [inst : NonUnitalNonAssocSemiring R] [inst_1 : Finite m]   [inst_2 :
 Finite n] {M : Matrix m …
· 使用定理 `Matrix.nondegenerate_of_det_ne_zero`：nondegenerate_of_det_ne_zero [NoZer
oDivisors R] (hM : M.det != 0) : M.Nondegenerate
-/
theorem eq_zero_of_vecMul_eq_zero [NoZeroDivisors R] (hM : M.det ≠ 0) {v : m → R}
    (hv : v ᵥ* M = 0) : v = 0 :=
  nondegenerate_of_det_ne_zero hM |>.separatingLeft.eq_zero_of_vecMul_eq_zero hv
/-
**Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `Matrix`。
形式化陈述：eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero (hM : M.det in R⁰) {v
 : m -> R} (hv : M *ᵥ v = 0) : v = 0
参数：hM : M.det in R⁰；hv : M *ᵥ v = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SeparatingRight.eq_zero_of_mulVec_eq_zero`：∀ {m : Type u_1} {n : 
Type u_2} {R : Type u_3} [inst : CommSemiring R] {M : Matrix m n R} [inst_1 : Fi
nite m]   [inst_2 : Fintype n], M.Sepa…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.Nondegenerate.separatingRight`：∀ {m : Type u_1} {n : Type u_2} {R
 : Type u_3} [inst : NonUnitalNonAssocSemiring R] [inst_1 : Finite m]   [inst_2 
: Finite n] {M : Matrix m …
· 使用定理 `Matrix.Nondegenerate.of_det_mem_nonZeroDivisors`：∀ {m : Type u_1} {R : T
ype u_2} [inst : CommRing R] [inst_1 : Fintype m] [inst_2 : DecidableEq m] {M : 
Matrix m m R},   M.det ∈ nonZeroDivis…
-/
theorem eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero (hM : M.det ∈ R⁰)
    {v : m → R} (hv : M *ᵥ v = 0) : v = 0 :=
  Nondegenerate.of_det_mem_nonZeroDivisors hM |>.separatingRight.eq_zero_of_mulVec_eq_zero hv
/-
**Matrix.eq_zero_of_mulVec_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eq_zero_of_mulVec_eq_zero [NoZeroDivisors R] (hM : M.det != 0) {v : m -> R
} (hv : M *ᵥ v = 0) : v = 0
参数：hM : M.det != 0；hv : M *ᵥ v = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SeparatingRight.eq_zero_of_mulVec_eq_zero`：∀ {m : Type u_1} {n : 
Type u_2} {R : Type u_3} [inst : CommSemiring R] {M : Matrix m n R} [inst_1 : Fi
nite m]   [inst_2 : Fintype n], M.Sepa…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.Nondegenerate.separatingRight`：∀ {m : Type u_1} {n : Type u_2} {R
 : Type u_3} [inst : NonUnitalNonAssocSemiring R] [inst_1 : Finite m]   [inst_2 
: Finite n] {M : Matrix m …
· 使用定理 `Matrix.nondegenerate_of_det_ne_zero`：nondegenerate_of_det_ne_zero [NoZer
oDivisors R] (hM : M.det != 0) : M.Nondegenerate
-/
theorem eq_zero_of_mulVec_eq_zero [NoZeroDivisors R] (hM : M.det ≠ 0) {v : m → R}
    (hv : M *ᵥ v = 0) : v = 0 :=
  nondegenerate_of_det_ne_zero hM |>.separatingRight.eq_zero_of_mulVec_eq_zero hv

/-- See also `Matrix.mulVec_injective_iff_isUnit` when working over a field. -/
/-
**Matrix.mulVec_injective_of_det_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix`。
形式化陈述：mulVec_injective_of_det_mem_nonZeroDivisors (hM : M.det in R⁰) : Function.
Injective M.mulVec
参数：hM : M.det in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero`：eq_zero_of_
det_mem_nonZeroDivisors_of_mulVec_eq_zero (hM : M.det in R⁰) {v : m -> R} (hv : 
M *ᵥ v = 0) : v = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_sub`：mulVec_sub [Fintype n] (A : Matrix m n α) (x y : n ->
 α) : A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
See also `Matrix.mulVec_injective_iff_isUnit` when working over a field.
-/
theorem mulVec_injective_of_det_mem_nonZeroDivisors (hM : M.det ∈ R⁰) :
    Function.Injective M.mulVec :=
  fun _ _ hxy => sub_eq_zero.mp
    (eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hM (by rw [mulVec_sub, hxy, sub_self]))
/-
**Matrix.mulVec_injective_of_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_injective_of_det_ne_zero [NoZeroDivisors R] (hM : M.det != 0) : Fun
ction.Injective M.mulVec
参数：hM : M.det != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mulVec_injective_of_det_mem_nonZeroDivisors`：mulVec_injective_of_
det_mem_nonZeroDivisors (hM : M.det in R⁰) : Function.Injective M.mulVec
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
-/
theorem mulVec_injective_of_det_ne_zero [NoZeroDivisors R] (hM : M.det ≠ 0) :
    Function.Injective M.mulVec :=
  mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hM)

end Determinant

end Matrix

open scoped Matrix in
/-
**LinearIndependent.sum_smul_of_nondegenerate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.sum_smul_of_nondegenerate {ι κ R M : Type*} [Fintype ι] 
[Finite κ] [CommRing R] [AddCommGroup M] [Module R M] {v : ι -> M} (hv : LinearI
ndependent R v) {A : Matrix κ ι R} (hA : A.Nondegenerate) : LinearIndependent R 
fun i => ∑ j, A i j • v j
参数：hv : LinearIndependent R v；hA : A.Nondegenerate。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.Nondegenerate.eq_zero_of_ortho`：∀ {m : Type u_1} {n : Type u_2} {
R : Type u_3} [inst : CommSemiring R] {M : Matrix m n R} [inst_1 : Fintype m]   
[inst_2 : Fintype n], M.Non…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma LinearIndependent.sum_smul_of_nondegenerate
    {ι κ R M : Type*} [Fintype ι] [Finite κ] [CommRing R] [AddCommGroup M] [Module R M]
    {v : ι → M} (hv : LinearIndependent R v)
    {A : Matrix κ ι R} (hA : A.Nondegenerate) :
    LinearIndependent R fun i ↦ ∑ j, A i j • v j := by
  have : Fintype κ := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro w hw
  suffices w = 0 by aesop
  simp_rw [Finset.smul_sum, ← smul_assoc] at hw
  rw [Finset.sum_comm] at hw
  simp_rw [← Finset.sum_smul] at hw
  replace hv : w ᵥ* A = 0 := funext <| hv _ hw
  replace hv (w' : ι → R) : w ⬝ᵥ A *ᵥ w' = 0 := by
    simpa [Matrix.dotProduct_mulVec] using congr_arg (fun x ↦ dotProduct x w') hv
  exact hA.eq_zero_of_ortho hv
