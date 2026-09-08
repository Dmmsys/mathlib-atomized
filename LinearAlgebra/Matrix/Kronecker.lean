/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Kronecker product of matrices

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `Matrix.kroneckerMap`: A generalization of the Kronecker product: given a map `f : α → β → γ`
  and matrices `A` and `B` with coefficients in `α` and `β`, respectively, it is defined as the
  matrix with coefficients in `γ` such that
  `kroneckerMap f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `Matrix.kroneckerMapBilinear`: when `f` is bilinear, so is `kroneckerMap f`.

## Specializations

* `Matrix.kronecker`: An alias of `kroneckerMap (*)`. Prefer using the notation.
* `Matrix.kroneckerBilinear`: `Matrix.kronecker` is bilinear

* `Matrix.kroneckerTMul`: An alias of `kroneckerMap (⊗ₜ)`. Prefer using the notation.
* `Matrix.kroneckerTMulBilinear`: `Matrix.kroneckerTMul` is bilinear

## Notation

These require `open Kronecker`:

* `A ⊗ₖ B` for `kroneckerMap (*) A B`. Lemmas about this notation use the token `kronecker`.
* `A ⊗ₖₜ B` and `A ⊗ₖₜ[R] B` for `kroneckerMap (⊗ₜ) A B`.
  Lemmas about this notation use the token `kroneckerTMul`.

-/

@[expose] public section


namespace Matrix
open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}
variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

section KroneckerMap

/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B`. -/
/-
**Matrix.kroneckerMap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β) : Mat
rix (l × n) (m × p) γ
参数：f : α -> β -> γ；A : Matrix l m α；B : Matrix n p β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce a matrix with `f` applied to every pair of elements from `A` and `B`.
-/
def kroneckerMap (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) : Matrix (l × n) (m × p) γ :=
  of fun (i : l × n) (j : m × p) => f (A i.1 j.1) (B i.2 j.2)

-- TODO: set as an equation lemma for `kroneckerMap`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**Matrix.kroneckerMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_apply (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β)
 (i j) : kroneckerMap f A B i j = f (A i.1 j.1) (B i.2 j.2)
参数：f : α -> β -> γ；A : Matrix l m α；B : Matrix n p β；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kroneckerMap_apply (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) (i j) :
    kroneckerMap f A B i j = f (A i.1 j.1) (B i.2 j.2) :=
  rfl
/-
**Matrix.kroneckerMap_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_transpose (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n 
p β) : kroneckerMap f Aᵀ Bᵀ = (kroneckerMap f A B)ᵀ
参数：f : α -> β -> γ；A : Matrix l m α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_transpose (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f Aᵀ Bᵀ = (kroneckerMap f A B)ᵀ :=
  ext fun _ _ => rfl
/-
**Matrix.kroneckerMap_map_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_map_left (f : α' -> β -> γ) (g : α -> α') (A : Matrix l m α) 
(B : Matrix n p β) : kroneckerMap f (A.map g) B = kroneckerMap (fun a b => f (g 
a) b) A B
参数：f : α' -> β -> γ；g : α -> α'；A : Matrix l m α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_map_left (f : α' → β → γ) (g : α → α') (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A.map g) B = kroneckerMap (fun a b => f (g a) b) A B :=
  ext fun _ _ => rfl
/-
**Matrix.kroneckerMap_map_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_map_right (f : α -> β' -> γ) (g : β -> β') (A : Matrix l m α)
 (B : Matrix n p β) : kroneckerMap f A (B.map g) = kroneckerMap (fun a b => f a 
(g b)) A B
参数：f : α -> β' -> γ；g : β -> β'；A : Matrix l m α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_map_right (f : α → β' → γ) (g : β → β') (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f A (B.map g) = kroneckerMap (fun a b => f a (g b)) A B :=
  ext fun _ _ => rfl
/-
**Matrix.kroneckerMap_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_map (f : α -> β -> γ) (g : γ -> γ') (A : Matrix l m α) (B : M
atrix n p β) : (kroneckerMap f A B).map g = kroneckerMap (fun a b => g (f a b)) 
A B
参数：f : α -> β -> γ；g : γ -> γ'；A : Matrix l m α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_map (f : α → β → γ) (g : γ → γ') (A : Matrix l m α) (B : Matrix n p β) :
    (kroneckerMap f A B).map g = kroneckerMap (fun a b => g (f a b)) A B :=
  ext fun _ _ => rfl
/-
**Matrix.kroneckerMap_submatrix_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_submatrix_left (f : α -> β -> γ) (A : Matrix l m α) (B : Matr
ix n p β) (r : l' -> l) (c : m' -> m) : kroneckerMap f (A.submatrix r c) B = (kr
oneckerMap f A B).submatrix (.map r id) (.map c id)
参数：f : α -> β -> γ；A : Matrix l m α；B : Matrix n p β；r : l' -> l；c : m' -> m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kroneckerMap_submatrix_left
    (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) (r : l' → l) (c : m' → m) :
    kroneckerMap f (A.submatrix r c) B =
      (kroneckerMap f A B).submatrix (.map r id) (.map c id) :=
  rfl
/-
**Matrix.kroneckerMap_submatrix_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_submatrix_right (f : α -> β -> γ) (A : Matrix l m α) (B : Mat
rix n p β) (r : n' -> n) (c : p' -> p) : kroneckerMap f A (B.submatrix r c) = (k
roneckerMap f A B).submatrix (.map id r) (.map id c)
参数：f : α -> β -> γ；A : Matrix l m α；B : Matrix n p β；r : n' -> n；c : p' -> p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kroneckerMap_submatrix_right
    (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) (r : n' → n) (c : p' → p) :
    kroneckerMap f A (B.submatrix r c) =
      (kroneckerMap f A B).submatrix (.map id r) (.map id c) :=
  rfl
/-
**Matrix.kroneckerMap_submatrix_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_submatrix_submatrix (f : α -> β -> γ) (A : Matrix l m α) (B :
 Matrix n p β) (r : l' -> l) (c : m' -> m) (r' : n' -> n) (c' : p' -> p) : krone
ckerMap f (A.submatrix r c) (B.submatrix r' c') = (kroneckerMap f A B).submatrix
 (.map r r') (.map c c')
参数：f : α -> β -> γ；A : Matrix l m α；B : Matrix n p β；r : l' -> l；c : m' -> m；r' 
: n' -> n；c' : p' -> p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kroneckerMap_submatrix_submatrix
    (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β)
    (r : l' → l) (c : m' → m) (r' : n' → n) (c' : p' → p) :
    kroneckerMap f (A.submatrix r c) (B.submatrix r' c') =
      (kroneckerMap f A B).submatrix (.map r r') (.map c c') :=
  rfl

@[simp]
/-
**Matrix.kroneckerMap_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_zero_left [Zero α] [Zero γ] (f : α -> β -> γ) (hf : forall b,
 f 0 b = 0) (B : Matrix n p β) : kroneckerMap f (0 : Matrix l m α) B = 0
参数：f : α -> β -> γ；hf : forall b, f 0 b = 0；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_zero_left [Zero α] [Zero γ] (f : α → β → γ) (hf : ∀ b, f 0 b = 0)
    (B : Matrix n p β) : kroneckerMap f (0 : Matrix l m α) B = 0 :=
  ext fun _ _ => hf _

@[simp]
/-
**Matrix.kroneckerMap_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_zero_right [Zero β] [Zero γ] (f : α -> β -> γ) (hf : forall a
, f a 0 = 0) (A : Matrix l m α) : kroneckerMap f A (0 : Matrix n p β) = 0
参数：f : α -> β -> γ；hf : forall a, f a 0 = 0；A : Matrix l m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_zero_right [Zero β] [Zero γ] (f : α → β → γ) (hf : ∀ a, f a 0 = 0)
    (A : Matrix l m α) : kroneckerMap f A (0 : Matrix n p β) = 0 :=
  ext fun _ _ => hf _
/-
**Matrix.kroneckerMap_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_add_left [Add α] [Add γ] (f : α -> β -> γ) (hf : forall a₁ a₂
 b, f (a₁ + a₂) b = f a₁ b + f a₂ b) (A₁ A₂ : Matrix l m α) (B : Matrix n p β) :
 kroneckerMap f (A₁ + A₂) B = kroneckerMap f A₁ B + kroneckerMap f A₂ B
参数：f : α -> β -> γ；hf : forall a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b；A₁ A₂ : 
Matrix l m α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_add_left [Add α] [Add γ] (f : α → β → γ)
    (hf : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) (A₁ A₂ : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A₁ + A₂) B = kroneckerMap f A₁ B + kroneckerMap f A₂ B :=
  ext fun _ _ => hf _ _ _
/-
**Matrix.kroneckerMap_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_add_right [Add β] [Add γ] (f : α -> β -> γ) (hf : forall a b₁
 b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) (A : Matrix l m α) (B₁ B₂ : Matrix n p β) 
: kroneckerMap f A (B₁ + B₂) = kroneckerMap f A B₁ + kroneckerMap f A B₂
参数：f : α -> β -> γ；hf : forall a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂；A : Matr
ix l m α；B₁ B₂ : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_add_right [Add β] [Add γ] (f : α → β → γ)
    (hf : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    kroneckerMap f A (B₁ + B₂) = kroneckerMap f A B₁ + kroneckerMap f A B₂ :=
  ext fun _ _ => hf _ _ _
/-
**Matrix.kroneckerMap_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_smul_left [SMul R α] [SMul R γ] (f : α -> β -> γ) (r : R) (hf
 : forall a b, f (r • a) b = r • f a b) (A : Matrix l m α) (B : Matrix n p β) : 
kroneckerMap f (r • A) B = r • kroneckerMap f A B
参数：f : α -> β -> γ；r : R；hf : forall a b, f (r • a) b = r • f a b；A : Matrix l m
 α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_smul_left [SMul R α] [SMul R γ] (f : α → β → γ) (r : R)
    (hf : ∀ a b, f (r • a) b = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (r • A) B = r • kroneckerMap f A B :=
  ext fun _ _ => hf _ _
/-
**Matrix.kroneckerMap_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_smul_right [SMul R β] [SMul R γ] (f : α -> β -> γ) (r : R) (h
f : forall a b, f a (r • b) = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
 kroneckerMap f A (r • B) = r • kroneckerMap f A B
参数：f : α -> β -> γ；r : R；hf : forall a b, f a (r • b) = r • f a b；A : Matrix l m
 α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_smul_right [SMul R β] [SMul R γ] (f : α → β → γ) (r : R)
    (hf : ∀ a b, f a (r • b) = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f A (r • B) = r • kroneckerMap f A B :=
  ext fun _ _ => hf _ _
/-
**Matrix.kroneckerMap_single_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_single_single [Zero α] [Zero β] [Zero γ] [DecidableEq l] [Dec
idableEq m] [DecidableEq n] [DecidableEq p] (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p) 
(f : α -> β -> γ) (hf₁ : forall b, f 0 b = 0) (hf₂ : forall a, f a 0 = 0) (a : α
) (b : β) : kroneckerMap f (single i₁ j₁ a) (single i₂ j₂ b) = single (i₁, i₂) (
j₁, j₂) (f a b)
参数：i₁ : l；j₁ : m；i₂ : n；j₂ : p；f : α -> β -> γ；hf₁ : forall b, f 0 b = 0；hf₂ : f
orall a, f a 0 = 0；a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_single_single
    [Zero α] [Zero β] [Zero γ] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p)
    (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : α) (b : β) :
    kroneckerMap f (single i₁ j₁ a) (single i₂ j₂ b) = single (i₁, i₂) (j₁, j₂) (f a b) := by
  ext ⟨i₁', i₂'⟩ ⟨j₁', j₂'⟩
  dsimp [single]
  grind
/-
**Matrix.kroneckerMap_diagonal_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_diagonal_diagonal [Zero α] [Zero β] [Zero γ] [DecidableEq m] 
[DecidableEq n] (f : α -> β -> γ) (hf₁ : forall b, f 0 b = 0) (hf₂ : forall a, f
 a 0 = 0) (a : m -> α) (b : n -> β) : kroneckerMap f (diagonal a) (diagonal b) =
 diagonal fun mn => f (a mn.1) (b mn.2)
参数：f : α -> β -> γ；hf₁ : forall b, f 0 b = 0；hf₂ : forall a, f a 0 = 0；a : m -> 
α；b : n -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_apply`：ite_apply (f g : forall a, σ a) (a : α) : (ite P f g) a = ite
 P (f a) (g a)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kroneckerMap_diagonal_diagonal [Zero α] [Zero β] [Zero γ] [DecidableEq m] [DecidableEq n]
    (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : m → α) (b : n → β) :
    kroneckerMap f (diagonal a) (diagonal b) = diagonal fun mn => f (a mn.1) (b mn.2) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂]
/-
**Matrix.kroneckerMap_diagonal_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_diagonal_right [Zero β] [Zero γ] [DecidableEq n] (f : α -> β 
-> γ) (hf : forall a, f a 0 = 0) (A : Matrix l m α) (b : n -> β) : kroneckerMap 
f A (diagonal b) = blockDiagonal fun i => A.map fun a => f a (b i)
参数：f : α -> β -> γ；hf : forall a, f a 0 = 0；A : Matrix l m α；b : n -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kroneckerMap_diagonal_right [Zero β] [Zero γ] [DecidableEq n] (f : α → β → γ)
    (hf : ∀ a, f a 0 = 0) (A : Matrix l m α) (b : n → β) :
    kroneckerMap f A (diagonal b) = blockDiagonal fun i => A.map fun a => f a (b i) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite (f (A i₁ j₁)), hf]
/-
**Matrix.kroneckerMap_diagonal_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_diagonal_left [Zero α] [Zero γ] [DecidableEq l] (f : α -> β -
> γ) (hf : forall b, f 0 b = 0) (a : l -> α) (B : Matrix m n β) : kroneckerMap f
 (diagonal a) B = Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (bloc
kDiagonal fun i => B.map fun b => f (a i) b)
参数：f : α -> β -> γ；hf : forall b, f 0 b = 0；a : l -> α；B : Matrix m n β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_apply`：ite_apply (f g : forall a, σ a) (a : α) : (ite P f g) a = ite
 P (f a) (g a)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kroneckerMap_diagonal_left [Zero α] [Zero γ] [DecidableEq l] (f : α → β → γ)
    (hf : ∀ b, f 0 b = 0) (a : l → α) (B : Matrix m n β) :
    kroneckerMap f (diagonal a) B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => f (a i) b) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite f, ite_apply, hf]

@[simp]
/-
**Matrix.kroneckerMap_one_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_one_one [Zero α] [Zero β] [Zero γ] [One α] [One β] [One γ] [D
ecidableEq m] [DecidableEq n] (f : α -> β -> γ) (hf₁ : forall b, f 0 b = 0) (hf₂
 : forall a, f a 0 = 0) (hf₃ : f 1 1 = 1) : kroneckerMap f (1 : Matrix m m α) (1
 : Matrix n n β) = 1
参数：f : α -> β -> γ；hf₁ : forall b, f 0 b = 0；hf₂ : forall a, f a 0 = 0；hf₃ : f 1
 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.kroneckerMap_diagonal_diagonal`：kroneckerMap_diagonal_diagonal [Z
ero α] [Zero β] [Zero γ] [DecidableEq m] [DecidableEq n] (f : α -> β -> γ) (hf₁ 
: forall b, f 0 b = 0) (hf₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kroneckerMap_one_one [Zero α] [Zero β] [Zero γ] [One α] [One β] [One γ] [DecidableEq m]
    [DecidableEq n] (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0)
    (hf₃ : f 1 1 = 1) : kroneckerMap f (1 : Matrix m m α) (1 : Matrix n n β) = 1 :=
  (kroneckerMap_diagonal_diagonal _ hf₁ hf₂ _ _).trans <| by simp only [hf₃, diagonal_one]
/-
**Matrix.kroneckerMap_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_reindex (f : α -> β -> γ) (el : l ≃ l') (em : m ≃ m') (en : n
 ≃ n') (ep : p ≃ p') (M : Matrix l m α) (N : Matrix n p β) : kroneckerMap f (rei
ndex el em M) (reindex en ep N) = reindex (el.prodCongr en) (em.prodCongr ep) (k
roneckerMap f M N)
参数：f : α -> β -> γ；el : l ≃ l'；em : m ≃ m'；en : n ≃ n'；ep : p ≃ p'；M : Matrix l 
m α；N : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem kroneckerMap_reindex (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p')
    (M : Matrix l m α) (N : Matrix n p β) :
    kroneckerMap f (reindex el em M) (reindex en ep N) =
      reindex (el.prodCongr en) (em.prodCongr ep) (kroneckerMap f M N) := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  rfl
/-
**Matrix.kroneckerMap_reindex_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_reindex_left (f : α -> β -> γ) (el : l ≃ l') (em : m ≃ m') (M
 : Matrix l m α) (N : Matrix n n' β) : kroneckerMap f (Matrix.reindex el em M) N
 = reindex (el.prodCongr (Equiv.refl _)) (em.prodCongr (Equiv.refl _)) (kronecke
rMap f M N)
参数：f : α -> β -> γ；el : l ≃ l'；em : m ≃ m'；M : Matrix l m α；N : Matrix n n' β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_reindex`：kroneckerMap_reindex (f : α -> β -> γ) (el 
: l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p') (M : Matrix l m α) (N : Matr
ix n p β) : krone…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem kroneckerMap_reindex_left (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (M : Matrix l m α)
    (N : Matrix n n' β) :
    kroneckerMap f (Matrix.reindex el em M) N =
      reindex (el.prodCongr (Equiv.refl _)) (em.prodCongr (Equiv.refl _)) (kroneckerMap f M N) :=
  kroneckerMap_reindex _ _ _ (Equiv.refl _) (Equiv.refl _) _ _
/-
**Matrix.kroneckerMap_reindex_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_reindex_right (f : α -> β -> γ) (em : m ≃ m') (en : n ≃ n') (
M : Matrix l l' α) (N : Matrix m n β) : kroneckerMap f M (reindex em en N) = rei
ndex ((Equiv.refl _).prodCongr em) ((Equiv.refl _).prodCongr en) (kroneckerMap f
 M N)
参数：f : α -> β -> γ；em : m ≃ m'；en : n ≃ n'；M : Matrix l l' α；N : Matrix m n β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_reindex`：kroneckerMap_reindex (f : α -> β -> γ) (el 
: l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p') (M : Matrix l m α) (N : Matr
ix n p β) : krone…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem kroneckerMap_reindex_right (f : α → β → γ) (em : m ≃ m') (en : n ≃ n') (M : Matrix l l' α)
    (N : Matrix m n β) :
    kroneckerMap f M (reindex em en N) =
      reindex ((Equiv.refl _).prodCongr em) ((Equiv.refl _).prodCongr en) (kroneckerMap f M N) :=
  kroneckerMap_reindex _ (Equiv.refl _) (Equiv.refl _) _ _ _ _
/-
**Matrix.kroneckerMap_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_assoc {δ ξ ω ω' : Type*} (f : α -> β -> γ) (g : γ -> δ -> ω) 
(f' : α -> ξ -> ω') (g' : β -> δ -> ξ) (A : Matrix l m α) (B : Matrix n p β) (D 
: Matrix q r δ) (φ : ω ≃ ω') (hφ : forall a b d, φ (g (f a b) d) = f' a (g' b d)
) : (reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)).trans (Equiv.mapMa
trix φ) (kroneckerMap g (kroneckerMap f A B) D) = kroneckerMap f' A (kroneckerMa
p g' B D)
参数：f : α -> β -> γ；g : γ -> δ -> ω；f' : α -> ξ -> ω'；g' : β -> δ -> ξ；A : Matrix
 l m α；B : Matrix n p β；D : Matrix q r δ；φ : ω ≃ ω'；hφ : forall a b d, φ (g (f a
 b) d) = f' a (g' b d)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem kroneckerMap_assoc {δ ξ ω ω' : Type*} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω')
    (g' : β → δ → ξ) (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ) (φ : ω ≃ ω')
    (hφ : ∀ a b d, φ (g (f a b) d) = f' a (g' b d)) :
    (reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)).trans (Equiv.mapMatrix φ)
        (kroneckerMap g (kroneckerMap f A B) D) =
      kroneckerMap f' A (kroneckerMap g' B D) :=
  ext fun _ _ => hφ _ _ _
/-
**Matrix.kroneckerMap_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMap_assoc {δ ξ ω ω' : Type*} (f : α -> β -> γ) (g : γ -> δ -> ω) 
(f' : α -> ξ -> ω') (g' : β -> δ -> ξ) (A : Matrix l m α) (B : Matrix n p β) (D 
: Matrix q r δ) (φ : ω ≃ ω') (hφ : forall a b d, φ (g (f a b) d) = f' a (g' b d)
) : (reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)).trans (Equiv.mapMa
trix φ) (kroneckerMap g (kroneckerMap f A B) D) = kroneckerMap f' A (kroneckerMa
p g' B D)
参数：f : α -> β -> γ；g : γ -> δ -> ω；f' : α -> ξ -> ω'；g' : β -> δ -> ξ；A : Matrix
 l m α；B : Matrix n p β；D : Matrix q r δ；φ : ω ≃ ω'；hφ : forall a b d, φ (g (f a
 b) d) = f' a (g' b d)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem kroneckerMap_assoc₁ {δ ξ ω : Type*} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω)
    (g' : β → δ → ξ) (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ)
    (h : ∀ a b d, g (f a b) d = f' a (g' b d)) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)
        (kroneckerMap g (kroneckerMap f A B) D) =
      kroneckerMap f' A (kroneckerMap g' B D) :=
  ext fun _ _ => h _ _ _

/-- When `f` is bilinear then `Matrix.kroneckerMap f` is also bilinear. -/
@[simps!]
/-
**Matrix.kroneckerMapBilinear** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerMapBilinear [Semiring S] [Semiring R] [AddCommMonoid α] [AddCommM
onoid β] [AddCommMonoid γ] [Module R α] [Module R γ] [Module S β] [Module S γ] [
SMulCommClass S R γ] (f : α ->ₗ[R] β ->ₗ[S] γ) : Matrix l m α ->ₗ[R] Matrix n p 
β ->ₗ[S] Matrix (l × n) (m × p) γ
参数：f : α ->ₗ[R] β ->ₗ[S] γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f` is bilinear then `Matrix.kroneckerMap f` is also bilinear.
-/
def kroneckerMapBilinear [Semiring S] [Semiring R]
    [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α →ₗ[R] β →ₗ[S] γ) :
    Matrix l m α →ₗ[R] Matrix n p β →ₗ[S] Matrix (l × n) (m × p) γ :=
  LinearMap.mk₂' R S (kroneckerMap fun r s => f r s) (kroneckerMap_add_left _ <| f.map_add₂)
    (fun _ => kroneckerMap_smul_left _ _ <| f.map_smul₂ _)
    (kroneckerMap_add_right _ fun a => (f a).map_add) fun r =>
    kroneckerMap_smul_right _ _ fun a => (f a).map_smul r

/-- `Matrix.kroneckerMapBilinear` commutes with `*` if `f` does.

This is primarily used with `R = ℕ` to prove `Matrix.mul_kronecker_mul`. -/
/-
**Matrix.kroneckerMapBilinear_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerMapBilinear_mul_mul [Semiring S] [Semiring R] [Fintype m] [Fintyp
e m'] [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [NonUnitalNonA
ssocSemiring γ] [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommCla
ss S R γ] (f : α ->ₗ[R] β ->ₗ[S] γ) (h_comm : forall a b a' b', f (a * b) (a' * 
b') = f a a' * f b b') (A : Matrix l m α) (B : Matrix m n α) (A' : Matrix l' m' 
β) (B' : Matrix m' n' β) : kroneckerMapBilinear f (A * B) (A' * B') = kroneckerM
apBilinear f A A' * kronec
参数：f : α ->ₗ[R] β ->ₗ[S] γ；h_comm : forall a b a' b', f (a * b) (a' * b') = f a 
a' * f b b'；A : Matrix l m α；B : Matrix m n α；A' : Matrix l' m' β；B' : Matrix m'
 n' β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.kroneckerMapBilinear_apply_apply`：∀ {R : Type u_1} {S : Type u_2}
 {α : Type u_3} {β : Type u_5} {γ : Type u_7} {l : Type u_9} {m : Type u_10}   {
n : Type u_11} {p : Type u_12…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Matrix.kroneckerMapBilinear` commutes with `*` if `f` does.

This is primarily used with `R = ℕ` to prove `Matrix.mul_kronecker_mul`.
-/
theorem kroneckerMapBilinear_mul_mul [Semiring S] [Semiring R] [Fintype m] [Fintype m']
    [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [NonUnitalNonAssocSemiring γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α →ₗ[R] β →ₗ[S] γ)
    (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b') (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    kroneckerMapBilinear f (A * B) (A' * B') =
      kroneckerMapBilinear f A A' * kroneckerMapBilinear f B B' := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [kroneckerMapBilinear_apply_apply, mul_apply, ← Finset.univ_product_univ,
    Finset.sum_product, kroneckerMap_apply]
  simp_rw [map_sum f, LinearMap.sum_apply, map_sum, h_comm]

/-- `trace` distributes over `Matrix.kroneckerMapBilinear`.

This is primarily used with `R = ℕ` to prove `Matrix.trace_kronecker`. -/
/-
**Matrix.trace_kroneckerMapBilinear** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_kroneckerMapBilinear [Semiring S] [Semiring R] [Fintype m] [Fintype 
n] [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ] [Module R α] [Module R 
γ] [Module S β] [Module S γ] [SMulCommClass S R γ] (f : α ->ₗ[R] β ->ₗ[S] γ) (A 
: Matrix m m α) (B : Matrix n n β) : trace (kroneckerMapBilinear f A B) = f (tra
ce A) (trace B)
参数：f : α ->ₗ[R] β ->ₗ[S] γ；A : Matrix m m α；B : Matrix n n β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.kroneckerMapBilinear_apply_apply`：∀ {R : Type u_1} {S : Type u_2}
 {α : Type u_3} {β : Type u_5} {γ : Type u_7} {l : Type u_9} {m : Type u_10}   {
n : Type u_11} {p : Type u_12…
· 使用定理 `LinearMap.map_sum₂`：map_sum₂ {ι : Type*} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
 (t : Finset ι) (x : ι -> M) (y) : f (∑ i in t, x i) y = ∑ i in t, f (x i) y
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`trace` distributes over `Matrix.kroneckerMapBilinear`.

This is primarily used with `R = ℕ` to prove `Matrix.trace_kronecker`.
-/
theorem trace_kroneckerMapBilinear [Semiring S] [Semiring R] [Fintype m] [Fintype n]
    [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α →ₗ[R] β →ₗ[S] γ)
    (A : Matrix m m α) (B : Matrix n n β) :
    trace (kroneckerMapBilinear f A B) = f (trace A) (trace B) := by
  simp_rw [Matrix.trace, Matrix.diag, kroneckerMapBilinear_apply_apply, LinearMap.map_sum₂,
    map_sum, ← Finset.univ_product_univ, Finset.sum_product, kroneckerMap_apply]

/-- `determinant` of `Matrix.kroneckerMapBilinear`.

This is primarily used with `R = ℕ` to prove `Matrix.det_kronecker`. -/
/-
**Matrix.det_kroneckerMapBilinear** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_kroneckerMapBilinear [Semiring S] [Semiring R] [Fintype m] [Fintype n]
 [DecidableEq m] [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β] [Comm
Ring γ] [Module R α] [Module S β] [Module R γ] [Module S γ] [SMulCommClass S R γ
] (f : α ->ₗ[R] β ->ₗ[S] γ) (h_comm : forall a b a' b', f (a * b) (a' * b') = f 
a a' * f b b') (A : Matrix m m α) (B : Matrix n n β) : det (kroneckerMapBilinear
 f A B) = det (A.map fun a => f a 1) ^ Fintype.card n * det (B.map fun b => f 1 
b) ^ Fintype.card m
参数：f : α ->ₗ[R] β ->ₗ[S] γ；h_comm : forall a b a' b', f (a * b) (a' * b') = f a 
a' * f b b'；A : Matrix m m α；B : Matrix n n β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.kroneckerMapBilinear_mul_mul`：kroneckerMapBilinear_mul_mul [Semir
ing S] [Semiring R] [Fintype m] [Fintype m'] [NonUnitalNonAssocSemiring α] [NonU
nitalNonAssocSemiring β] …
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用定理 `Matrix.kroneckerMapBilinear_apply_apply`：∀ {R : Type u_1} {S : Type u_2}
 {α : Type u_3} {β : Type u_5} {γ : Type u_7} {l : Type u_9} {m : Type u_10}   {
n : Type u_11} {p : Type u_12…
· 使用定理 `Matrix.kroneckerMap_diagonal_right`：kroneckerMap_diagonal_right [Zero β]
 [Zero γ] [DecidableEq n] (f : α -> β -> γ) (hf : forall a, f a 0 = 0) (A : Matr
ix l m α) (b : n -> β) :…
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
· 使用定理 `Matrix.kroneckerMap_diagonal_left`：kroneckerMap_diagonal_left [Zero α] [
Zero γ] [DecidableEq l] (f : α -> β -> γ) (hf : forall b, f 0 b = 0) (a : l -> α
) (B : Matrix m n β) : …
· 使用定理 `LinearMap.map_zero₂`：map_zero₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (y) : f 0
 y = 0
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det_blockDiagonal`：det_blockDiagonal {o : Type*} [Fintype o] [Dec
idableEq o] (M : o -> Matrix n n R) : (blockDiagonal M).det = ∏ k, (M k).det
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`determinant` of `Matrix.kroneckerMapBilinear`.

This is primarily used with `R = ℕ` to prove `Matrix.det_kronecker`.
-/
theorem det_kroneckerMapBilinear [Semiring S] [Semiring R] [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β] [CommRing γ] [Module R α] [Module S β]
    [Module R γ] [Module S γ] [SMulCommClass S R γ]
    (f : α →ₗ[R] β →ₗ[S] γ) (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b')
    (A : Matrix m m α) (B : Matrix n n β) :
    det (kroneckerMapBilinear f A B) =
      det (A.map fun a => f a 1) ^ Fintype.card n * det (B.map fun b => f 1 b) ^ Fintype.card m :=
  calc
    det (kroneckerMapBilinear f A B) =
        det (kroneckerMapBilinear f A 1 * kroneckerMapBilinear f 1 B) := by
      rw [← kroneckerMapBilinear_mul_mul f h_comm, Matrix.mul_one, Matrix.one_mul]
    _ = det (blockDiagonal fun (_ : n) => A.map fun a => f a 1) *
        det (blockDiagonal fun (_ : m) => B.map fun b => f 1 b) := by
      rw [det_mul, ← diagonal_one, ← diagonal_one, kroneckerMapBilinear_apply_apply,
        kroneckerMap_diagonal_right _ fun _ => _, kroneckerMapBilinear_apply_apply,
        kroneckerMap_diagonal_left _ fun _ => _, det_reindex_self]
      · intro; exact LinearMap.map_zero₂ _ _
      · intro; exact map_zero _
    _ = _ := by simp_rw [det_blockDiagonal, Finset.prod_const, Finset.card_univ]

end KroneckerMap

/-! ### Specialization to `Matrix.kroneckerMap (*)` -/


section Kronecker

open Matrix

/-- The Kronecker product. This is just a shorthand for `kroneckerMap (*)`. Prefer the notation
`⊗ₖ` rather than this definition. -/
@[simp]
/-
**Matrix.kronecker** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kronecker [Mul α] : Matrix l m α -> Matrix n p α -> Matrix (l × n) (m × p)
 α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Kronecker product. This is just a shorthand for `kroneckerMap (*)`. Prefer t
he notation
`⊗ₖ` rather than this definition.
-/
def kronecker [Mul α] : Matrix l m α → Matrix n p α → Matrix (l × n) (m × p) α :=
  kroneckerMap (· * ·)

@[inherit_doc Matrix.kroneckerMap]
scoped[Kronecker] infixl:100 " ⊗ₖ " => Matrix.kroneckerMap (· * ·)

open Kronecker

@[simp]
/-
**Matrix.kronecker_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_apply [Mul α] (A : Matrix l m α) (B : Matrix n p α) (i₁ i₂ j₁ j₂
) : (A otimesₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂
参数：A : Matrix l m α；B : Matrix n p α；i₁ i₂ j₁ j₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kronecker_apply [Mul α] (A : Matrix l m α) (B : Matrix n p α) (i₁ i₂ j₁ j₂) :
    (A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂ :=
  rfl

/-- `Matrix.kronecker` as a bilinear map. -/
/-
**Matrix.kroneckerBilinear** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerBilinear [CommSemiring R] [Semiring α] [Algebra R α] : Matrix l m
 α ->ₗ[R] Matrix n p α ->ₗ[R] Matrix (l × n) (m × p) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.kronecker` as a bilinear map.
-/
def kroneckerBilinear [CommSemiring R] [Semiring α] [Algebra R α] :
    Matrix l m α →ₗ[R] Matrix n p α →ₗ[R] Matrix (l × n) (m × p) α :=
  kroneckerMapBilinear (Algebra.lmul R α)

/-! What follows is a copy, in order, of every `Matrix.kroneckerMap` lemma above that has
hypotheses which can be filled by properties of `*`. -/


/-
**Matrix.zero_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zero_kronecker [MulZeroClass α] (B : Matrix n p α) : (0 : Matrix l m α) ot
imesₖ B = 0
参数：B : Matrix n p α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_zero_left`：kroneckerMap_zero_left [Zero α] [Zero γ] 
(f : α -> β -> γ) (hf : forall b, f 0 b = 0) (B : Matrix n p β) : kroneckerMap f
 (0 : Matrix l m α)…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
What follows is a copy, in order, of every `Matrix.kroneckerMap` lemma above tha
t has
hypotheses which can be filled by properties of `*`.
-/
theorem zero_kronecker [MulZeroClass α] (B : Matrix n p α) : (0 : Matrix l m α) ⊗ₖ B = 0 :=
  kroneckerMap_zero_left _ zero_mul B
/-
**Matrix.kronecker_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_zero [MulZeroClass α] (A : Matrix l m α) : A otimesₖ (0 : Matrix
 n p α) = 0
参数：A : Matrix l m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_zero_right`：kroneckerMap_zero_right [Zero β] [Zero γ
] (f : α -> β -> γ) (hf : forall a, f a 0 = 0) (A : Matrix l m α) : kroneckerMap
 f A (0 : Matrix n p…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem kronecker_zero [MulZeroClass α] (A : Matrix l m α) : A ⊗ₖ (0 : Matrix n p α) = 0 :=
  kroneckerMap_zero_right _ mul_zero A
/-
**Matrix.add_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_kronecker [Distrib α] (A₁ A₂ : Matrix l m α) (B : Matrix n p α) : (A₁ 
+ A₂) otimesₖ B = A₁ otimesₖ B + A₂ otimesₖ B
参数：A₁ A₂ : Matrix l m α；B : Matrix n p α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_add_left`：kroneckerMap_add_left [Add α] [Add γ] (f :
 α -> β -> γ) (hf : forall a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) (A₁ A₂ : Ma
trix l m α) (B : M…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem add_kronecker [Distrib α] (A₁ A₂ : Matrix l m α) (B : Matrix n p α) :
    (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B :=
  kroneckerMap_add_left _ add_mul _ _ _
/-
**Matrix.kronecker_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_add [Distrib α] (A : Matrix l m α) (B₁ B₂ : Matrix n p α) : A ot
imesₖ (B₁ + B₂) = A otimesₖ B₁ + A otimesₖ B₂
参数：A : Matrix l m α；B₁ B₂ : Matrix n p α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_add_right`：kroneckerMap_add_right [Add β] [Add γ] (f
 : α -> β -> γ) (hf : forall a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) (A : Matr
ix l m α) (B₁ B₂ : …
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem kronecker_add [Distrib α] (A : Matrix l m α) (B₁ B₂ : Matrix n p α) :
    A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ :=
  kroneckerMap_add_right _ mul_add _ _ _
/-
**Matrix.smul_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_kronecker [Mul α] [SMul R α] [IsScalarTower R α α] (r : R) (A : Matri
x l m α) (B : Matrix n p α) : (r • A) otimesₖ B = r • A otimesₖ B
参数：r : R；A : Matrix l m α；B : Matrix n p α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_smul_left`：kroneckerMap_smul_left [SMul R α] [SMul R
 γ] (f : α -> β -> γ) (r : R) (hf : forall a b, f (r • a) b = r • f a b) (A : Ma
trix l m α) (B : Ma…
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
theorem smul_kronecker [Mul α] [SMul R α] [IsScalarTower R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : (r • A) ⊗ₖ B = r • A ⊗ₖ B :=
  kroneckerMap_smul_left _ _ (fun _ _ => smul_mul_assoc _ _ _) _ _
/-
**Matrix.kronecker_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_smul [Mul α] [SMul R α] [SMulCommClass R α α] (r : R) (A : Matri
x l m α) (B : Matrix n p α) : A otimesₖ (r • B) = r • A otimesₖ B
参数：r : R；A : Matrix l m α；B : Matrix n p α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_smul_right`：kroneckerMap_smul_right [SMul R β] [SMul
 R γ] (f : α -> β -> γ) (r : R) (hf : forall a b, f a (r • b) = r • f a b) (A : 
Matrix l m α) (B : M…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
-/
theorem kronecker_smul [Mul α] [SMul R α] [SMulCommClass R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : A ⊗ₖ (r • B) = r • A ⊗ₖ B :=
  kroneckerMap_smul_right _ _ (fun _ _ => mul_smul_comm _ _ _) _ _
/-
**Matrix.single_kronecker_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_kronecker_single [MulZeroClass α] [DecidableEq l] [DecidableEq m] [
DecidableEq n] [DecidableEq p] (ia : l) (ja : m) (ib : n) (jb : p) (a b : α) : s
ingle ia ja a otimesₖ single ib jb b = single (ia, ib) (ja, jb) (a * b)
参数：ia : l；ja : m；ib : n；jb : p；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_single_single`：kroneckerMap_single_single [Zero α] [
Zero β] [Zero γ] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
 (i₁ : l) (j₁ : m) (i₂ …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem single_kronecker_single
    [MulZeroClass α] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ia : l) (ja : m) (ib : n) (jb : p) (a b : α) :
    single ia ja a ⊗ₖ single ib jb b = single (ia, ib) (ja, jb) (a * b) :=
  kroneckerMap_single_single _ _ _ _ _ zero_mul mul_zero _ _
/-
**Matrix.diagonal_kronecker_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_kronecker_diagonal [MulZeroClass α] [DecidableEq m] [DecidableEq 
n] (a : m -> α) (b : n -> α) : diagonal a otimesₖ diagonal b = diagonal fun mn =
> a mn.1 * b mn.2
参数：a : m -> α；b : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_diagonal_diagonal`：kroneckerMap_diagonal_diagonal [Z
ero α] [Zero β] [Zero γ] [DecidableEq m] [DecidableEq n] (f : α -> β -> γ) (hf₁ 
: forall b, f 0 b = 0) (hf₂…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem diagonal_kronecker_diagonal [MulZeroClass α] [DecidableEq m] [DecidableEq n] (a : m → α)
    (b : n → α) : diagonal a ⊗ₖ diagonal b = diagonal fun mn => a mn.1 * b mn.2 :=
  kroneckerMap_diagonal_diagonal _ zero_mul mul_zero _ _
/-
**Matrix.kronecker_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_diagonal [MulZeroClass α] [DecidableEq n] (A : Matrix l m α) (b 
: n -> α) : A otimesₖ diagonal b = blockDiagonal fun i => A <• b i
参数：A : Matrix l m α；b : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_diagonal_right`：kroneckerMap_diagonal_right [Zero β]
 [Zero γ] [DecidableEq n] (f : α -> β -> γ) (hf : forall a, f a 0 = 0) (A : Matr
ix l m α) (b : n -> β) :…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem kronecker_diagonal [MulZeroClass α] [DecidableEq n] (A : Matrix l m α) (b : n → α) :
    A ⊗ₖ diagonal b = blockDiagonal fun i => A <• b i :=
  kroneckerMap_diagonal_right _ mul_zero _ _
/-
**Matrix.diagonal_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_kronecker [MulZeroClass α] [DecidableEq l] (a : l -> α) (B : Matr
ix m n α) : diagonal a otimesₖ B = Matrix.reindex (Equiv.prodComm _ _) (Equiv.pr
odComm _ _) (blockDiagonal fun i => a i • B)
参数：a : l -> α；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_diagonal_left`：kroneckerMap_diagonal_left [Zero α] [
Zero γ] [DecidableEq l] (f : α -> β -> γ) (hf : forall b, f 0 b = 0) (a : l -> α
) (B : Matrix m n β) : …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem diagonal_kronecker [MulZeroClass α] [DecidableEq l] (a : l → α) (B : Matrix m n α) :
    diagonal a ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun i => a i • B) :=
  kroneckerMap_diagonal_left _ zero_mul _ _

@[simp]
/-
**Matrix.natCast_kronecker_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：natCast_kronecker_natCast [NonAssocSemiring α] [DecidableEq m] [DecidableE
q n] (a b : Nat) : (a : Matrix m m α) otimesₖ (b : Matrix n n α) = ↑(a * b)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.diagonal_kronecker_diagonal`：diagonal_kronecker_diagonal [MulZero
Class α] [DecidableEq m] [DecidableEq n] (a : m -> α) (b : n -> α) : diagonal a 
otimesₖ diagonal b = dia…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem natCast_kronecker_natCast [NonAssocSemiring α] [DecidableEq m] [DecidableEq n] (a b : ℕ) :
    (a : Matrix m m α) ⊗ₖ (b : Matrix n n α) = ↑(a * b) :=
  (diagonal_kronecker_diagonal _ _).trans <| by simp_rw [← Nat.cast_mul]; rfl
/-
**Matrix.kronecker_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_natCast [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) 
(b : Nat) : A otimesₖ (b : Matrix n n α) = blockDiagonal fun _ => b • A
参数：A : Matrix l m α；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.kronecker_diagonal`：kronecker_diagonal [MulZeroClass α] [Decidabl
eEq n] (A : Matrix l m α) (b : n -> α) : A otimesₖ diagonal b = blockDiagonal fu
n i => A <• b i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kronecker_natCast [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : ℕ) :
    A ⊗ₖ (b : Matrix n n α) = blockDiagonal fun _ => b • A :=
  kronecker_diagonal _ _ |>.trans <| by
    congr! 2
    ext
    simp [(Nat.cast_commute b _).eq]
/-
**Matrix.natCast_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：natCast_kronecker [NonAssocSemiring α] [DecidableEq l] (a : Nat) (B : Matr
ix m n α) : (a : Matrix l l α) otimesₖ B = Matrix.reindex (Equiv.prodComm _ _) (
Equiv.prodComm _ _) (blockDiagonal fun _ => a • B)
参数：a : Nat；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.diagonal_kronecker`：diagonal_kronecker [MulZeroClass α] [Decidabl
eEq l] (a : l -> α) (B : Matrix m n α) : diagonal a otimesₖ B = Matrix.reindex (
Equiv.prodComm …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCast_kronecker [NonAssocSemiring α] [DecidableEq l] (a : ℕ) (B : Matrix m n α) :
    (a : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun _ => a • B) :=
  diagonal_kronecker _ _ |>.trans <| by
    congr! 2
    ext
    simp [(Nat.cast_commute a _).eq]
/-
**Matrix.kronecker_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_ofNat [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b
 : Nat) [b.AtLeastTwo] : A otimesₖ (ofNat(b) : Matrix n n α) = blockDiagonal fun
 _ => A <• (ofNat(b) : α)
参数：A : Matrix l m α；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kronecker_diagonal`：kronecker_diagonal [MulZeroClass α] [Decidabl
eEq n] (A : Matrix l m α) (b : n -> α) : A otimesₖ diagonal b = blockDiagonal fu
n i => A <• b i
-/
theorem kronecker_ofNat [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : ℕ)
    [b.AtLeastTwo] : A ⊗ₖ (ofNat(b) : Matrix n n α) =
      blockDiagonal fun _ => A <• (ofNat(b) : α) :=
  kronecker_diagonal _ _
/-
**Matrix.ofNat_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofNat_kronecker [NonAssocSemiring α] [DecidableEq l] (a : Nat) [a.AtLeastT
wo] (B : Matrix m n α) : (ofNat(a) : Matrix l l α) otimesₖ B = Matrix.reindex (.
prodComm _ _) (.prodComm _ _) (blockDiagonal fun _ => (ofNat(a) : α) • B)
参数：a : Nat；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_kronecker`：diagonal_kronecker [MulZeroClass α] [Decidabl
eEq l] (a : l -> α) (B : Matrix m n α) : diagonal a otimesₖ B = Matrix.reindex (
Equiv.prodComm …
-/
theorem ofNat_kronecker [NonAssocSemiring α] [DecidableEq l] (a : ℕ) [a.AtLeastTwo]
    (B : Matrix m n α) : (ofNat(a) : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (.prodComm _ _) (.prodComm _ _)
        (blockDiagonal fun _ => (ofNat(a) : α) • B) :=
  diagonal_kronecker _ _
/-
**Matrix.one_kronecker_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_kronecker_one [MulZeroOneClass α] [DecidableEq m] [DecidableEq n] : (1
 : Matrix m m α) otimesₖ (1 : Matrix n n α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_one_one`：kroneckerMap_one_one [Zero α] [Zero β] [Zer
o γ] [One α] [One β] [One γ] [DecidableEq m] [DecidableEq n] (f : α -> β -> γ) (
hf₁ : forall b, f…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_kronecker_one [MulZeroOneClass α] [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) ⊗ₖ (1 : Matrix n n α) = 1 :=
  kroneckerMap_one_one _ zero_mul mul_zero (one_mul _)
/-
**Matrix.kronecker_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_one [MulZeroOneClass α] [DecidableEq n] (A : Matrix l m α) : A o
timesₖ (1 : Matrix n n α) = blockDiagonal fun _ => A
参数：A : Matrix l m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.kronecker_diagonal`：kronecker_diagonal [MulZeroClass α] [Decidabl
eEq n] (A : Matrix l m α) (b : n -> α) : A otimesₖ diagonal b = blockDiagonal fu
n i => A <• b i
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem kronecker_one [MulZeroOneClass α] [DecidableEq n] (A : Matrix l m α) :
    A ⊗ₖ (1 : Matrix n n α) = blockDiagonal fun _ => A :=
  (kronecker_diagonal _ _).trans <| congr_arg _ <| funext fun _ => Matrix.ext fun _ _ => mul_one _
/-
**Matrix.one_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_kronecker [MulZeroOneClass α] [DecidableEq l] (B : Matrix m n α) : (1 
: Matrix l l α) otimesₖ B = Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm 
_ _) (blockDiagonal fun _ => B)
参数：B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.diagonal_kronecker`：diagonal_kronecker [MulZeroClass α] [Decidabl
eEq l] (a : l -> α) (B : Matrix m n α) : diagonal a otimesₖ B = Matrix.reindex (
Equiv.prodComm …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_kronecker [MulZeroOneClass α] [DecidableEq l] (B : Matrix m n α) :
    (1 : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun _ => B) :=
  (diagonal_kronecker _ _).trans <|
    congr_arg _ <| congr_arg _ <| funext fun _ => Matrix.ext fun _ _ => one_mul _
/-
**Matrix.mul_kronecker_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_kronecker_mul [Fintype m] [Fintype m'] [CommSemiring α] (A : Matrix l 
m α) (B : Matrix m n α) (A' : Matrix l' m' α) (B' : Matrix m' n' α) : (A * B) ot
imesₖ (A' * B') = A otimesₖ A' * B otimesₖ B'
参数：A : Matrix l m α；B : Matrix m n α；A' : Matrix l' m' α；B' : Matrix m' n' α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMapBilinear_mul_mul`：kroneckerMapBilinear_mul_mul [Semir
ing S] [Semiring R] [Fintype m] [Fintype m'] [NonUnitalNonAssocSemiring α] [NonU
nitalNonAssocSemiring β] …
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
-/
theorem mul_kronecker_mul [Fintype m] [Fintype m'] [CommSemiring α] (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' α) (B' : Matrix m' n' α) :
    (A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B' :=
  kroneckerMapBilinear_mul_mul (Algebra.lmul ℕ α).toLinearMap mul_mul_mul_comm A B A' B'

-- simp-normal form is `kronecker_assoc'`
/-
**Matrix.kronecker_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_assoc [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : M
atrix q r α) : reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r) (A otimes
ₖ B otimesₖ C) = A otimesₖ (B otimesₖ C)
参数：A : Matrix l m α；B : Matrix n p α；C : Matrix q r α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_assoc₁`：kroneckerMap_assoc₁ {δ ξ ω : Type*} (f : α -
> β -> γ) (g : γ -> δ -> ω) (f' : α -> ξ -> ω) (g' : β -> δ -> ξ) (A : Matrix l 
m α) (B : Matrix…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem kronecker_assoc [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r) (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) :=
  kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

@[simp]
/-
**Matrix.kronecker_assoc'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_assoc' [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : 
Matrix q r α) : submatrix (A otimesₖ B otimesₖ C) (Equiv.prodAssoc l n q).symm (
Equiv.prodAssoc m p r).symm = A otimesₖ (B otimesₖ C)
参数：A : Matrix l m α；B : Matrix n p α；C : Matrix q r α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_assoc₁`：kroneckerMap_assoc₁ {δ ξ ω : Type*} (f : α -
> β -> γ) (g : γ -> δ -> ω) (f' : α -> ξ -> ω) (g' : β -> δ -> ξ) (A : Matrix l 
m α) (B : Matrix…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem kronecker_assoc' [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α) :
    submatrix (A ⊗ₖ B ⊗ₖ C) (Equiv.prodAssoc l n q).symm (Equiv.prodAssoc m p r).symm =
    A ⊗ₖ (B ⊗ₖ C) :=
  kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc
/-
**Matrix.trace_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_kronecker [Fintype m] [Fintype n] [Semiring α] (A : Matrix m m α) (B
 : Matrix n n α) : trace (A otimesₖ B) = trace A * trace B
参数：A : Matrix m m α；B : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_kroneckerMapBilinear`：trace_kroneckerMapBilinear [Semiring 
S] [Semiring R] [Fintype m] [Fintype n] [AddCommMonoid α] [AddCommMonoid β] [Add
CommMonoid γ] [Module R…
-/
theorem trace_kronecker [Fintype m] [Fintype n] [Semiring α] (A : Matrix m m α) (B : Matrix n n α) :
    trace (A ⊗ₖ B) = trace A * trace B :=
  trace_kroneckerMapBilinear (Algebra.lmul ℕ α).toLinearMap _ _
/-
**Matrix.det_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_kronecker [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Com
mRing R] (A : Matrix m m R) (B : Matrix n n R) : det (A otimesₖ B) = det A ^ Fin
type.card n * det B ^ Fintype.card m
参数：A : Matrix m m R；B : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_kroneckerMapBilinear`：det_kroneckerMapBilinear [Semiring S] [
Semiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [NonAssocSem
iring α] [NonAssocSem…
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.map_id'`：map_id' (M : Matrix m n α) : M.map (·) = M
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_kronecker [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : Matrix m m R) (B : Matrix n n R) :
    det (A ⊗ₖ B) = det A ^ Fintype.card n * det B ^ Fintype.card m := by
  refine (det_kroneckerMapBilinear (Algebra.lmul ℕ R).toLinearMap mul_mul_mul_comm _ _).trans ?_
  simp
/-
**Matrix.conjTranspose_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_kronecker [CommMagma R] [StarMul R] (x : Matrix l m R) (y : 
Matrix n p R) : (x otimesₖ y)ᴴ = xᴴ otimesₖ yᴴ
参数：x : Matrix l m R；y : Matrix n p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_mul'`：star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) 
= star x * star y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjTranspose_kronecker [CommMagma R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x ⊗ₖ y)ᴴ = xᴴ ⊗ₖ yᴴ := by
  ext; simp
/-
**Matrix.conjTranspose_kronecker'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_kronecker' [Mul R] [StarMul R] (x : Matrix l m R) (y : Matri
x n p R) : (x otimesₖ y)ᴴ = (yᴴ otimesₖ xᴴ).submatrix Prod.swap Prod.swap
参数：x : Matrix l m R；y : Matrix n p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjTranspose_kronecker' [Mul R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x ⊗ₖ y)ᴴ = (yᴴ ⊗ₖ xᴴ).submatrix Prod.swap Prod.swap := by
  ext; simp

end Kronecker

/-! ### Specialization to `Matrix.kroneckerMap (⊗ₜ)` -/


section KroneckerTmul

variable (R)

open TensorProduct

open Matrix TensorProduct

section Module

variable [CommSemiring R]
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module R β] [Module R γ]

/-- The Kronecker tensor product. This is just a shorthand for `kroneckerMap (⊗ₜ)`.
Prefer the notation `⊗ₖₜ` rather than this definition. -/
@[simp]
/-
**Matrix.kroneckerTMul** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul : Matrix l m α -> Matrix n p β -> Matrix (l × n) (m × p) (α 
otimes[R] β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Kronecker tensor product. This is just a shorthand for `kroneckerMap (⊗ₜ)`.
Prefer the notation `⊗ₖₜ` rather than this definition.
-/
def kroneckerTMul : Matrix l m α → Matrix n p β → Matrix (l × n) (m × p) (α ⊗[R] β) :=
  kroneckerMap (· ⊗ₜ ·)

@[inherit_doc kroneckerTMul]
scoped[Kronecker] infixl:100 " ⊗ₖₜ " => Matrix.kroneckerMap (TensorProduct.tmul _)

@[inherit_doc kroneckerTMul] scoped[Kronecker] notation:100 x " ⊗ₖₜ[" R "] " y:100 =>
  Matrix.kroneckerMap (TensorProduct.tmul R) x y

open Kronecker

@[simp]
/-
**Matrix.kroneckerTMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul_apply (A : Matrix l m α) (B : Matrix n p β) (i₁ i₂ j₁ j₂) : 
(A otimesₖₜ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ otimesₜ[R] B i₂ j₂
参数：A : Matrix l m α；B : Matrix n p β；i₁ i₂ j₁ j₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kroneckerTMul_apply (A : Matrix l m α) (B : Matrix n p β) (i₁ i₂ j₁ j₂) :
    (A ⊗ₖₜ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ ⊗ₜ[R] B i₂ j₂ :=
  rfl

variable (S) in
/-- `Matrix.kronecker` as a bilinear map. -/
/-
**Matrix.kroneckerTMulBilinear** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMulBilinear [Semiring S] [Module S α] [SMulCommClass R S α] : Ma
trix l m α ->ₗ[S] Matrix n p β ->ₗ[R] Matrix (l × n) (m × p) (α otimes[R] β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.kronecker` as a bilinear map.
-/
def kroneckerTMulBilinear [Semiring S] [Module S α] [SMulCommClass R S α] :
    Matrix l m α →ₗ[S] Matrix n p β →ₗ[R] Matrix (l × n) (m × p) (α ⊗[R] β) :=
  kroneckerMapBilinear (AlgebraTensorModule.mk _ _ α β)

@[simp]
/-
**Matrix.kroneckerTMulBilinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMulBilinear_apply [Semiring S] [Module S α] [SMulCommClass R S α
] (A : Matrix l m α) (B : Matrix n p β) : kroneckerTMulBilinear R S A B = A otim
esₖₜ[R] B
参数：A : Matrix l m α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kroneckerTMulBilinear_apply [Semiring S] [Module S α] [SMulCommClass R S α]
    (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerTMulBilinear R S A B = A ⊗ₖₜ[R] B := rfl

/-! What follows is a copy, in order, of every `Matrix.kroneckerMap` lemma above that has
hypotheses which can be filled by properties of `⊗ₜ`. -/


/-
**Matrix.zero_kroneckerTMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zero_kroneckerTMul (B : Matrix n p β) : (0 : Matrix l m α) otimesₖₜ[R] B =
 0
参数：B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_zero_left`：kroneckerMap_zero_left [Zero α] [Zero γ] 
(f : α -> β -> γ) (hf : forall b, f 0 b = 0) (B : Matrix n p β) : kroneckerMap f
 (0 : Matrix l m α)…
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0

--- 原说明 ---
What follows is a copy, in order, of every `Matrix.kroneckerMap` lemma above tha
t has
hypotheses which can be filled by properties of `⊗ₜ`.
-/
theorem zero_kroneckerTMul (B : Matrix n p β) : (0 : Matrix l m α) ⊗ₖₜ[R] B = 0 :=
  kroneckerMap_zero_left _ (zero_tmul α) B
/-
**Matrix.kroneckerTMul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul_zero (A : Matrix l m α) : A otimesₖₜ[R] (0 : Matrix n p β) =
 0
参数：A : Matrix l m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_zero_right`：kroneckerMap_zero_right [Zero β] [Zero γ
] (f : α -> β -> γ) (hf : forall a, f a 0 = 0) (A : Matrix l m α) : kroneckerMap
 f A (0 : Matrix n p…
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
-/
theorem kroneckerTMul_zero (A : Matrix l m α) : A ⊗ₖₜ[R] (0 : Matrix n p β) = 0 :=
  kroneckerMap_zero_right _ (tmul_zero β) A
/-
**Matrix.add_kroneckerTMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_kroneckerTMul (A₁ A₂ : Matrix l m α) (B : Matrix n p α) : (A₁ + A₂) ot
imesₖₜ[R] B = A₁ otimesₖₜ B + A₂ otimesₖₜ B
参数：A₁ A₂ : Matrix l m α；B : Matrix n p α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_add_left`：kroneckerMap_add_left [Add α] [Add γ] (f :
 α -> β -> γ) (hf : forall a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) (A₁ A₂ : Ma
trix l m α) (B : M…
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
-/
theorem add_kroneckerTMul (A₁ A₂ : Matrix l m α) (B : Matrix n p α) :
    (A₁ + A₂) ⊗ₖₜ[R] B = A₁ ⊗ₖₜ B + A₂ ⊗ₖₜ B :=
  kroneckerMap_add_left _ add_tmul _ _ _
/-
**Matrix.kroneckerTMul_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul_add (A : Matrix l m α) (B₁ B₂ : Matrix n p β) : A otimesₖₜ[R
] (B₁ + B₂) = A otimesₖₜ B₁ + A otimesₖₜ B₂
参数：A : Matrix l m α；B₁ B₂ : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_add_right`：kroneckerMap_add_right [Add β] [Add γ] (f
 : α -> β -> γ) (hf : forall a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) (A : Matr
ix l m α) (B₁ B₂ : …
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
-/
theorem kroneckerTMul_add (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    A ⊗ₖₜ[R] (B₁ + B₂) = A ⊗ₖₜ B₁ + A ⊗ₖₜ B₂ :=
  kroneckerMap_add_right _ tmul_add _ _ _
/-
**Matrix.smul_kroneckerTMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_kroneckerTMul [Monoid S] [DistribMulAction S α] [SMulCommClass R S α]
 (r : S) (A : Matrix l m α) (B : Matrix n p β) : (r • A) otimesₖₜ[R] B = r • A o
timesₖₜ[R] B
参数：r : S；A : Matrix l m α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_smul_left`：kroneckerMap_smul_left [SMul R α] [SMul R
 γ] (f : α -> β -> γ) (r : R) (hf : forall a b, f (r • a) b = r • f a b) (A : Ma
trix l m α) (B : Ma…
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
-/
theorem smul_kroneckerTMul [Monoid S] [DistribMulAction S α] [SMulCommClass R S α]
    (r : S) (A : Matrix l m α) (B : Matrix n p β) :
    (r • A) ⊗ₖₜ[R] B = r • A ⊗ₖₜ[R] B :=
  kroneckerMap_smul_left _ _ (fun _ _ => smul_tmul' _ _ _) _ _
/-
**Matrix.kroneckerTMul_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul_smul [Monoid S] [DistribMulAction S α] [DistribMulAction S β
] [SMul S R] [SMulCommClass R S α] [IsScalarTower S R α] [IsScalarTower S R β] (
r : S) (A : Matrix l m α) (B : Matrix n p β) : A otimesₖₜ[R] (r • B) = r • A oti
mesₖₜ[R] B
参数：r : S；A : Matrix l m α；B : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_smul_right`：kroneckerMap_smul_right [SMul R β] [SMul
 R γ] (f : α -> β -> γ) (r : R) (hf : forall a b, f a (r • b) = r • f a b) (A : 
Matrix l m α) (B : M…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
theorem kroneckerTMul_smul [Monoid S] [DistribMulAction S α] [DistribMulAction S β]
    [SMul S R] [SMulCommClass R S α] [IsScalarTower S R α] [IsScalarTower S R β]
    (r : S) (A : Matrix l m α) (B : Matrix n p β) :
    A ⊗ₖₜ[R] (r • B) = r • A ⊗ₖₜ[R] B :=
  kroneckerMap_smul_right _ _ (fun _ _ => tmul_smul _ _ _) _ _
/-
**Matrix.single_kroneckerTMul_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_kroneckerTMul_single [DecidableEq l] [DecidableEq m] [DecidableEq n
] [DecidableEq p] (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p) (a : α) (b : β) : single i
₁ j₁ a otimesₖₜ[R] single i₂ j₂ b = single (i₁, i₂) (j₁, j₂) (a otimesₜ b)
参数：i₁ : l；j₁ : m；i₂ : n；j₂ : p；a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_single_single`：kroneckerMap_single_single [Zero α] [
Zero β] [Zero γ] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
 (i₁ : l) (j₁ : m) (i₂ …
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
-/
theorem single_kroneckerTMul_single
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p) (a : α) (b : β) :
    single i₁ j₁ a ⊗ₖₜ[R] single i₂ j₂ b = single (i₁, i₂) (j₁, j₂) (a ⊗ₜ b) :=
  kroneckerMap_single_single _ _ _ _ _ (zero_tmul _) (tmul_zero _) _ _
/-
**Matrix.diagonal_kroneckerTMul_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_kroneckerTMul_diagonal [DecidableEq m] [DecidableEq n] (a : m -> 
α) (b : n -> β) : diagonal a otimesₖₜ[R] diagonal b = diagonal fun mn => a mn.1 
otimesₜ b mn.2
参数：a : m -> α；b : n -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_diagonal_diagonal`：kroneckerMap_diagonal_diagonal [Z
ero α] [Zero β] [Zero γ] [DecidableEq m] [DecidableEq n] (f : α -> β -> γ) (hf₁ 
: forall b, f 0 b = 0) (hf₂…
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
-/
theorem diagonal_kroneckerTMul_diagonal [DecidableEq m] [DecidableEq n] (a : m → α) (b : n → β) :
    diagonal a ⊗ₖₜ[R] diagonal b = diagonal fun mn => a mn.1 ⊗ₜ b mn.2 :=
  kroneckerMap_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _
/-
**Matrix.kroneckerTMul_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul_diagonal [DecidableEq n] (A : Matrix l m α) (b : n -> β) : A
 otimesₖₜ[R] diagonal b = blockDiagonal fun i => A.map fun a => a otimesₜ[R] b i
参数：A : Matrix l m α；b : n -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_diagonal_right`：kroneckerMap_diagonal_right [Zero β]
 [Zero γ] [DecidableEq n] (f : α -> β -> γ) (hf : forall a, f a 0 = 0) (A : Matr
ix l m α) (b : n -> β) :…
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
-/
theorem kroneckerTMul_diagonal [DecidableEq n] (A : Matrix l m α) (b : n → β) :
    A ⊗ₖₜ[R] diagonal b = blockDiagonal fun i => A.map fun a => a ⊗ₜ[R] b i :=
  kroneckerMap_diagonal_right _ (tmul_zero _) _ _
/-
**Matrix.diagonal_kroneckerTMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_kroneckerTMul [DecidableEq l] (a : l -> α) (B : Matrix m n β) : d
iagonal a otimesₖₜ[R] B = Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ 
_) (blockDiagonal fun i => B.map fun b => a i otimesₜ[R] b)
参数：a : l -> α；B : Matrix m n β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_diagonal_left`：kroneckerMap_diagonal_left [Zero α] [
Zero γ] [DecidableEq l] (f : α -> β -> γ) (hf : forall b, f 0 b = 0) (a : l -> α
) (B : Matrix m n β) : …
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
-/
theorem diagonal_kroneckerTMul [DecidableEq l] (a : l → α) (B : Matrix m n β) :
    diagonal a ⊗ₖₜ[R] B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => a i ⊗ₜ[R] b) :=
  kroneckerMap_diagonal_left _ (zero_tmul _) _ _

-- simp-normal form is `kroneckerTMul_assoc'`
/-
**Matrix.kroneckerTMul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul_assoc (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r 
γ) : reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r) (((A otimesₖₜ[R] B)
 otimesₖₜ[R] C).map (TensorProduct.assoc R α β γ)) = A otimesₖₜ[R] B otimesₖₜ[R]
 C
参数：A : Matrix l m α；B : Matrix n p β；C : Matrix q r γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `TensorProduct.assoc_tmul`：assoc_tmul (m : M) (n : N) (p : P) : (TensorPr
oduct.assoc R M N P) (m otimesₜ n otimesₜ p) = m otimesₜ (n otimesₜ p)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem kroneckerTMul_assoc (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)
        (((A ⊗ₖₜ[R] B) ⊗ₖₜ[R] C).map (TensorProduct.assoc R α β γ)) =
      A ⊗ₖₜ[R] B ⊗ₖₜ[R] C :=
  ext fun _ _ => assoc_tmul _ _ _

@[simp]
/-
**Matrix.kroneckerTMul_assoc'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul_assoc' (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r
 γ) : submatrix (((A otimesₖₜ[R] B) otimesₖₜ[R] C).map (TensorProduct.assoc R α 
β γ)) (Equiv.prodAssoc l n q).symm (Equiv.prodAssoc m p r).symm = A otimesₖₜ[R] 
B otimesₖₜ[R] C
参数：A : Matrix l m α；B : Matrix n p β；C : Matrix q r γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `TensorProduct.assoc_tmul`：assoc_tmul (m : M) (n : N) (p : P) : (TensorPr
oduct.assoc R M N P) (m otimesₜ n otimesₜ p) = m otimesₜ (n otimesₜ p)
-/
theorem kroneckerTMul_assoc' (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ) :
    submatrix (((A ⊗ₖₜ[R] B) ⊗ₖₜ[R] C).map (TensorProduct.assoc R α β γ))
      (Equiv.prodAssoc l n q).symm (Equiv.prodAssoc m p r).symm = A ⊗ₖₜ[R] B ⊗ₖₜ[R] C :=
  ext fun _ _ => assoc_tmul _ _ _
/-
**Matrix.trace_kroneckerTMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_kroneckerTMul [Fintype m] [Fintype n] (A : Matrix m m α) (B : Matrix
 n n β) : trace (A otimesₖₜ[R] B) = trace A otimesₜ[R] trace B
参数：A : Matrix m m α；B : Matrix n n β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_kroneckerMapBilinear`：trace_kroneckerMapBilinear [Semiring 
S] [Semiring R] [Fintype m] [Fintype n] [AddCommMonoid α] [AddCommMonoid β] [Add
CommMonoid γ] [Module R…
-/
theorem trace_kroneckerTMul [Fintype m] [Fintype n] (A : Matrix m m α) (B : Matrix n n β) :
    trace (A ⊗ₖₜ[R] B) = trace A ⊗ₜ[R] trace B :=
  trace_kroneckerMapBilinear (TensorProduct.mk R α β) _ _
/-
**Matrix.conjTranspose_kroneckerTMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_kroneckerTMul [StarRing R] [StarAddMonoid α] [StarAddMonoid 
β] [StarModule R α] [StarModule R β] (x : Matrix l m α) (y : Matrix n p β) : (x 
otimesₖₜ[R] y)ᴴ = xᴴ otimesₖₜ[R] yᴴ
参数：x : Matrix l m α；y : Matrix n p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjTranspose_kroneckerTMul [StarRing R] [StarAddMonoid α] [StarAddMonoid β]
    [StarModule R α] [StarModule R β] (x : Matrix l m α) (y : Matrix n p β) :
    (x ⊗ₖₜ[R] y)ᴴ = xᴴ ⊗ₖₜ[R] yᴴ := by
  ext; simp

end Module

section Algebra

open Kronecker

open Algebra.TensorProduct

section Semiring
variable [CommSemiring R]

@[simp]
/-
**Matrix.one_kroneckerTMul_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_kroneckerTMul_one [AddCommMonoidWithOne α] [AddCommMonoidWithOne β] [M
odule R α] [Module R β] [DecidableEq m] [DecidableEq n] : (1 : Matrix m m α) oti
mesₖₜ[R] (1 : Matrix n n β) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMap_one_one`：kroneckerMap_one_one [Zero α] [Zero β] [Zer
o γ] [One α] [One β] [One γ] [DecidableEq m] [DecidableEq n] (f : α -> β -> γ) (
hf₁ : forall b, f…
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
-/
theorem one_kroneckerTMul_one
    [AddCommMonoidWithOne α] [AddCommMonoidWithOne β] [Module R α] [Module R β]
    [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) ⊗ₖₜ[R] (1 : Matrix n n β) = 1 :=
  kroneckerMap_one_one _ (zero_tmul _) (tmul_zero _) rfl

unseal mul in
/-
**Matrix.mul_kroneckerTMul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_kroneckerTMul_mul [NonUnitalSemiring α] [NonUnitalSemiring β] [Module 
R α] [Module R β] [IsScalarTower R α α] [SMulCommClass R α α] [IsScalarTower R β
 β] [SMulCommClass R β β] [Fintype m] [Fintype m'] (A : Matrix l m α) (B : Matri
x m n α) (A' : Matrix l' m' β) (B' : Matrix m' n' β) : (A * B) otimesₖₜ[R] (A' *
 B') = A otimesₖₜ[R] A' * B otimesₖₜ[R] B'
参数：A : Matrix l m α；B : Matrix m n α；A' : Matrix l' m' β；B' : Matrix m' n' β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kroneckerMapBilinear_mul_mul`：kroneckerMapBilinear_mul_mul [Semir
ing S] [Semiring R] [Fintype m] [Fintype m'] [NonUnitalNonAssocSemiring α] [NonU
nitalNonAssocSemiring β] …
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
-/
theorem mul_kroneckerTMul_mul
    [NonUnitalSemiring α] [NonUnitalSemiring β] [Module R α] [Module R β]
    [IsScalarTower R α α] [SMulCommClass R α α] [IsScalarTower R β β] [SMulCommClass R β β]
    [Fintype m] [Fintype m'] (A : Matrix l m α) (B : Matrix m n α)
    (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    (A * B) ⊗ₖₜ[R] (A' * B') = A ⊗ₖₜ[R] A' * B ⊗ₖₜ[R] B' :=
  kroneckerMapBilinear_mul_mul (TensorProduct.mk R α β) tmul_mul_tmul A B A' B'

end Semiring

section CommRing

variable [CommRing R] [CommRing α] [CommRing β] [Algebra R α] [Algebra R β]

unseal mul in
/-
**Matrix.det_kroneckerTMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_kroneckerTMul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] 
(A : Matrix m m α) (B : Matrix n n β) : det (A otimesₖₜ[R] B) = (det A ^ Fintype
.card n) otimesₜ[R] (det B ^ Fintype.card m)
参数：A : Matrix m m α；B : Matrix n n β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_kroneckerMapBilinear`：det_kroneckerMapBilinear [Semiring S] [
Semiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [NonAssocSem
iring α] [NonAssocSem…
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.TensorProduct.includeLeft_apply`：includeLeft_apply [SMulCommClas
s R S A] (a : A) : (includeLeft : A ->ₐ[S] A otimes[R] B) a = a otimesₜ 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.TensorProduct.tmul_pow`：tmul_pow (a : A) (b : B) (k : Nat) : a o
timesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_kroneckerTMul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m α) (B : Matrix n n β) :
    det (A ⊗ₖₜ[R] B) = (det A ^ Fintype.card n) ⊗ₜ[R] (det B ^ Fintype.card m) := by
  refine (det_kroneckerMapBilinear (TensorProduct.mk R α β) tmul_mul_tmul _ _).trans ?_
  simp -eta only [mk_apply, ← includeLeft_apply (S := R), ← includeRight_apply]
  simp only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  simp only [includeLeft_apply, includeRight_apply, tmul_pow, tmul_mul_tmul, one_pow,
    _root_.mul_one, _root_.one_mul]

end CommRing

end Algebra

-- insert lemmas specific to `kroneckerTMul` below this line
end KroneckerTmul

end Matrix

