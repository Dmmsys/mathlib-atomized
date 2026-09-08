/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.RingEquiv
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.DedekindFinite

/-!
# Matrices

This file contains basic results on matrices including bundled versions of matrix operators.

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/

@[expose] public section

assert_not_exists TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R S T A α β γ : Type*}

namespace Matrix

/-
**Matrix.decidableEq** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：decidableEq [DecidableEq α] [Fintype m] [Fintype n] : DecidableEq (Matrix 
m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEq [DecidableEq α] [Fintype m] [Fintype n] : DecidableEq (Matrix m n α) :=
  Fintype.decidablePiFintype
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (α) [Fintype α] :
    Fintype (Matrix m n α) := inferInstanceAs (Fintype (m → n → α))
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n m} [Finite m] [Finite n] (α) [Finite α] :
    Finite (Matrix m n α) := inferInstanceAs (Finite (m → n → α))
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Semiring α] [Finite α] : IsStablyFiniteRing α := ⟨inferInstance⟩

section
variable (R)

/-- This is `Matrix.of` bundled as a linear equivalence. -/
/-
**Matrix.ofLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：ofLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] : (m -> n -> α) 
≃ₗ[R] Matrix m n α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `Matrix.of` bundled as a linear equivalence.
-/
def ofLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] : (m → n → α) ≃ₗ[R] Matrix m n α where
  __ := ofAddEquiv
  map_smul' _ _ := rfl
/-
**Matrix.coe_ofLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_7) {α : Type u_11} [inst : Sem
iring R] [inst_1 : AddCommMonoid α]   [inst_2 : _root_.Module R α], ⇑(Matrix.ofL
inearEquiv R) = ⇑Matrix.of
参数：R : Type u_7；Matrix.ofLinearEquiv R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] :
    ⇑(ofLinearEquiv _ : (m → n → α) ≃ₗ[R] Matrix m n α) = of := rfl
/-
**Matrix.coe_ofLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_7) {α : Type u_11} [inst : Sem
iring R] [inst_1 : AddCommMonoid α]   [inst_2 : _root_.Module R α], ⇑(Matrix.ofL
inearEquiv R).symm = ⇑Matrix.of.symm
参数：R : Type u_7；Matrix.ofLinearEquiv R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    ⇑((ofLinearEquiv _).symm : Matrix m n α ≃ₗ[R] (m → n → α)) = of.symm := rfl

end

/-
**Matrix.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β -> Matri
x m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
参数：i : m；j : n；s : Finset β；g : β -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
-/
theorem sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β → Matrix m n α) :
    (∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j :=
  (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

end Matrix

open Matrix

namespace Matrix

section Diagonal

variable [DecidableEq n]

variable (n α)

/-- `Matrix.diagonal` as an `AddMonoidHom`. -/
@[simps]
/-
**Matrix.diagonalAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagonalAddMonoidHom [AddZeroClass α] : (n -> α) ->+ Matrix n n α where to
Fun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.diagonal` as an `AddMonoidHom`.
-/
def diagonalAddMonoidHom [AddZeroClass α] : (n → α) →+ Matrix n n α where
  toFun := diagonal
  map_zero' := diagonal_zero
  map_add' x y := (diagonal_add x y).symm

variable (R)

/-- `Matrix.diagonal` as a `LinearMap`. -/
@[simps]
/-
**Matrix.diagonalLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagonalLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : (n -> α) -
>ₗ[R] Matrix n n α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.diagonal` as a `LinearMap`.
-/
def diagonalLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : (n → α) →ₗ[R] Matrix n n α :=
  { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }

variable {n α R}

section One

variable [Zero α] [One α]

/-
**Matrix.zero_le_one_elem** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：zero_le_one_elem [Preorder α] [ZeroLEOneClass α] (i j : n) : 0 <= (1 : Mat
rix n n α) i j
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma zero_le_one_elem [Preorder α] [ZeroLEOneClass α] (i j : n) :
    0 ≤ (1 : Matrix n n α) i j := by
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]
/-
**Matrix.zero_le_one_row** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：zero_le_one_row [Preorder α] [ZeroLEOneClass α] (i : n) : 0 <= (1 : Matrix
 n n α) i
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.zero_le_one_elem`：zero_le_one_elem [Preorder α] [ZeroLEOneClass α
] (i j : n) : 0 <= (1 : Matrix n n α) i j
-/
lemma zero_le_one_row [Preorder α] [ZeroLEOneClass α] (i : n) :
    0 ≤ (1 : Matrix n n α) i :=
  zero_le_one_elem i

end One

end Diagonal

section Diag

variable (n α)

/-- `Matrix.diag` as an `AddMonoidHom`. -/
@[simps]
/-
**Matrix.diagAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagAddMonoidHom [AddZeroClass α] : Matrix n n α ->+ n -> α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.diag` as an `AddMonoidHom`.
-/
def diagAddMonoidHom [AddZeroClass α] : Matrix n n α →+ n → α where
  toFun := diag
  map_zero' := diag_zero
  map_add' := diag_add

variable (R)

/-- `Matrix.diag` as a `LinearMap`. -/
@[simps]
/-
**Matrix.diagLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : Matrix n n α -
>ₗ[R] n -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.diag` as a `LinearMap`.
-/
def diagLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : Matrix n n α →ₗ[R] n → α :=
  { diagAddMonoidHom n α with map_smul' := diag_smul }

variable {n α R}

@[simp]
/-
**Matrix.diag_list_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_list_sum [AddMonoid α] (l : List (Matrix n n α)) : diag l.sum = (l.ma
p diag).sum
参数：l : List (Matrix n n α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem diag_list_sum [AddMonoid α] (l : List (Matrix n n α)) : diag l.sum = (l.map diag).sum :=
  map_list_sum (diagAddMonoidHom n α) l

@[simp]
/-
**Matrix.diag_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix n n α)) : diag s
.sum = (s.map diag).sum
参数：s : Multiset (Matrix n n α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem diag_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix n n α)) :
    diag s.sum = (s.map diag).sum :=
  map_multiset_sum (diagAddMonoidHom n α) s

@[simp]
/-
**Matrix.diag_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_sum {ι} [AddCommMonoid α] (s : Finset ι) (f : ι -> Matrix n n α) : di
ag (∑ i in s, f i) = ∑ i in s, diag (f i)
参数：s : Finset ι；f : ι -> Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem diag_sum {ι} [AddCommMonoid α] (s : Finset ι) (f : ι → Matrix n n α) :
    diag (∑ i ∈ s, f i) = ∑ i ∈ s, diag (f i) :=
  map_sum (diagAddMonoidHom n α) f s

end Diag

open Matrix

section NonAssocSemiring

variable [NonAssocSemiring α]

variable (α n)

/-- `Matrix.diagonal` as a `RingHom`. -/
@[simps]
/-
**Matrix.diagonalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagonalRingHom [Fintype n] [DecidableEq n] : (n -> α) ->+* Matrix n n α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.diagonal` as a `RingHom`.
-/
def diagonalRingHom [Fintype n] [DecidableEq n] : (n → α) →+* Matrix n n α :=
  { diagonalAddMonoidHom n α with
    toFun := diagonal
    map_one' := diagonal_one
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }

end NonAssocSemiring

section Semiring

variable [Semiring α]

/-
**Matrix.diagonal_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_pow [Fintype n] [DecidableEq n] (v : n -> α) (k : Nat) : diagonal
 v ^ k = diagonal (v ^ k)
参数：v : n -> α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem diagonal_pow [Fintype n] [DecidableEq n] (v : n → α) (k : ℕ) :
    diagonal v ^ k = diagonal (v ^ k) :=
  (map_pow (diagonalRingHom n α) v k).symm

/-- The ring homomorphism `α →+* Matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
/-
**Matrix.scalar** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：scalar (n : Type u) [DecidableEq n] [Fintype n] : α ->+* Matrix n n α
参数：n : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism `α →+* Matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [DecidableEq n] [Fintype n] : α →+* Matrix n n α :=
  (diagonalRingHom n α).comp <| Pi.constRingHom n α

section Scalar

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

@[simp]
/-
**Matrix.scalar_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：scalar_apply (a : α) : scalar n a = diagonal fun _ => a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem scalar_apply (a : α) : scalar n a = diagonal fun _ => a :=
  rfl
/-
**Matrix.scalar_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：scalar_inj [Nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Matrix.diagonal_injective`：diagonal_injective [Zero α] : Function.Inject
ive (diagonal : (n -> α) -> Matrix n n α)
· 使用定理 `Function.const_injective`：const_injective [Nonempty α] : Injective (cons
t α : β -> α -> β)
-/
theorem scalar_inj [Nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s :=
  (diagonal_injective.comp Function.const_injective).eq_iff

/-- A version of `Matrix.scalar_commute_iff` for rectangular matrices. -/
/-
**Matrix.scalar_comm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：scalar_comm_iff {r : α} {M : Matrix m n α} : scalar m r * M = M * scalar n
 r ↔ r • M = MulOpposite.op r • M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A version of `Matrix.scalar_commute_iff` for rectangular matrices.
-/
theorem scalar_comm_iff {r : α} {M : Matrix m n α} :
    scalar m r * M = M * scalar n r ↔ r • M = MulOpposite.op r • M := by
  simp_rw [scalar_apply, ← smul_eq_diagonal_mul, ← op_smul_eq_mul_diagonal]
/-
**Matrix.scalar_commute_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：scalar_commute_iff {r : α} {M : Matrix n n α} : Commute (scalar n r) M ↔ r
 • M = MulOpposite.op r • M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.scalar_comm_iff`：scalar_comm_iff {r : α} {M : Matrix m n α} : sca
lar m r * M = M * scalar n r ↔ r • M = MulOpposite.op r • M
-/
theorem scalar_commute_iff {r : α} {M : Matrix n n α} :
    Commute (scalar n r) M ↔ r • M = MulOpposite.op r • M :=
  scalar_comm_iff

/-- A version of `Matrix.scalar_commute` for rectangular matrices. -/
/-
**Matrix.scalar_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：scalar_comm (r : α) (hr : forall r', Commute r r') (M : Matrix m n α) : sc
alar m r * M = M * scalar n r
参数：r : α；hr : forall r', Commute r r'；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.scalar_comm_iff`：scalar_comm_iff {r : α} {M : Matrix m n α} : sca
lar m r * M = M * scalar n r ↔ r • M = MulOpposite.op r • M
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N

--- 原说明 ---
A version of `Matrix.scalar_commute` for rectangular matrices.
-/
theorem scalar_comm (r : α) (hr : ∀ r', Commute r r') (M : Matrix m n α) :
    scalar m r * M = M * scalar n r :=
  scalar_comm_iff.2 <| ext fun _ _ => hr _
/-
**Matrix.scalar_commute** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：scalar_commute (r : α) (hr : forall r', Commute r r') (M : Matrix n n α) :
 Commute (scalar n r) M
参数：r : α；hr : forall r', Commute r r'；M : Matrix n n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.scalar_comm`：scalar_comm (r : α) (hr : forall r', Commute r r') (
M : Matrix m n α) : scalar m r * M = M * scalar n r
-/
theorem scalar_commute (r : α) (hr : ∀ r', Commute r r') (M : Matrix n n α) :
    Commute (scalar n r) M := scalar_comm r hr M

end Scalar

end Semiring

section Algebra

variable [Fintype n] [DecidableEq n]
variable [CommSemiring R] [Semiring α] [Semiring β] [Algebra R α] [Algebra R β]

/-
**Matrix.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instAlgebra : Algebra R (Matrix n n α) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra : Algebra R (Matrix n n α) where
  algebraMap := (Matrix.scalar n).comp (algebraMap R α)
  commutes' _ _ := scalar_commute _ (fun _ => Algebra.commutes _ _) _
  smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]
/-
**Matrix.algebraMap_matrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：algebraMap_matrix_apply {r : R} {i j : n} : algebraMap R (Matrix n n α) r 
i j = if i = j then algebraMap R α r else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_matrix_apply {r : R} {i j : n} :
    algebraMap R (Matrix n n α) r i j = if i = j then algebraMap R α r else 0 := rfl
/-
**Matrix.algebraMap_eq_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：algebraMap_eq_diagonal (r : R) : algebraMap R (Matrix n n α) r = diagonal 
(algebraMap R (n -> α) r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_diagonal (r : R) :
    algebraMap R (Matrix n n α) r = diagonal (algebraMap R (n → α) r) := rfl
/-
**Matrix.algebraMap_eq_diagonalRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：algebraMap_eq_diagonalRingHom : algebraMap R (Matrix n n α) = (diagonalRin
gHom n α).comp (algebraMap R _)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_diagonalRingHom :
    algebraMap R (Matrix n n α) = (diagonalRingHom n α).comp (algebraMap R _) := rfl

@[simp]
/-
**Matrix.map_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_algebraMap (r : R) (f : α -> β) (hf : f 0 = 0) (hf₂ : f (algebraMap R 
α r) = algebraMap R β r) : (algebraMap R (Matrix n n α) r).map f = algebraMap R 
(Matrix n n β) r
参数：r : R；f : α -> β；hf : f 0 = 0；hf₂ : f (algebraMap R α r) = algebraMap R β r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.algebraMap_eq_diagonal`：algebraMap_eq_diagonal (r : R) : algebraM
ap R (Matrix n n α) r = diagonal (algebraMap R (n -> α) r)
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem map_algebraMap (r : R) (f : α → β) (hf : f 0 = 0)
    (hf₂ : f (algebraMap R α r) = algebraMap R β r) :
    (algebraMap R (Matrix n n α) r).map f = algebraMap R (Matrix n n β) r := by
  rw [algebraMap_eq_diagonal, algebraMap_eq_diagonal, diagonal_map hf]
  simp [hf₂]

variable (R)

/-- `Matrix.diagonal` as an `AlgHom`. -/
@[simps]
/-
**Matrix.diagonalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagonalAlgHom : (n -> α) ->ₐ[R] Matrix n n α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.diagonal` as an `AlgHom`.
-/
def diagonalAlgHom : (n → α) →ₐ[R] Matrix n n α :=
  { diagonalRingHom n α with
    toFun := diagonal
    commutes' := fun r => (algebraMap_eq_diagonal r).symm }

variable (n)

/-- `Matrix.scalar` as an `AlgHom`. -/
/-
**Matrix.scalarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：scalarAlgHom : α ->ₐ[R] Matrix n n α where toRingHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.scalar` as an `AlgHom`.
-/
def scalarAlgHom : α →ₐ[R] Matrix n n α where
  toRingHom := scalar n
  commutes' _ := rfl
/-
**Matrix.scalarAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ (n : Type u_3) (R : Type u_7) {α : Type u_11} [inst : Fintype n] [inst_1
 : DecidableEq n] [inst_2 : CommSemiring R]   [inst_3 : Semiring α] [inst_4 : Al
gebra R α] (a : α), (Matrix.scalarAlgHom n R) a = (Matrix.scalar n) a
参数：n : Type u_3；R : Type u_7；a : α；Matrix.scalarAlgHom n R；Matrix.scalar n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem scalarAlgHom_apply (a : α) : scalarAlgHom n R a = scalar n a := rfl

end Algebra

section AddHom

variable [Add α]

variable (R α) in
/-- Extracting entries from a matrix as an additive homomorphism. -/
@[simps]
/-
**Matrix.entryAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：entryAddHom (i : m) (j : n) : AddHom (Matrix m n α) α where toFun M
参数：i : m；j : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extracting entries from a matrix as an additive homomorphism.
-/
def entryAddHom (i : m) (j : n) : AddHom (Matrix m n α) α where
  toFun M := M i j
  map_add' _ _ := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
/-
**Matrix.entryAddHom_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：entryAddHom_eq_comp {i : m} {j : n} : entryAddHom α i j = ((Pi.evalAddHom 
(fun _ => α) j).comp (Pi.evalAddHom _ i)).comp (AddHomClass.toAddHom ofAddEquiv.
symm)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma entryAddHom_eq_comp {i : m} {j : n} :
    entryAddHom α i j =
      ((Pi.evalAddHom (fun _ => α) j).comp (Pi.evalAddHom _ i)).comp
        (AddHomClass.toAddHom ofAddEquiv.symm) :=
  rfl

end AddHom

section AddMonoidHom

variable [AddZeroClass α]

variable (R α) in
/--
Extracting entries from a matrix as an additive monoid homomorphism. Note this cannot be upgraded to
a ring homomorphism, as it does not respect multiplication.
-/
@[simps]
/-
**Matrix.entryAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：entryAddMonoidHom (i : m) (j : n) : Matrix m n α ->+ α where toFun M
参数：i : m；j : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extracting entries from a matrix as an additive monoid homomorphism. Note this c
annot be upgraded to
a ring homomorphism, as it does not respect multiplication.
-/
def entryAddMonoidHom (i : m) (j : n) : Matrix m n α →+ α where
  toFun M := M i j
  map_add' _ _ := rfl
  map_zero' := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
/-
**Matrix.entryAddMonoidHom_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：entryAddMonoidHom_eq_comp {i : m} {j : n} : entryAddMonoidHom α i j = ((Pi
.evalAddMonoidHom (fun _ => α) j).comp (Pi.evalAddMonoidHom _ i)).comp (AddMonoi
dHomClass.toAddMonoidHom ofAddEquiv.symm)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma entryAddMonoidHom_eq_comp {i : m} {j : n} :
    entryAddMonoidHom α i j =
      ((Pi.evalAddMonoidHom (fun _ => α) j).comp (Pi.evalAddMonoidHom _ i)).comp
        (AddMonoidHomClass.toAddMonoidHom ofAddEquiv.symm) := by
  rfl
/-
**Matrix.evalAddMonoidHom_comp_diagAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x`。
形式化陈述：∀ {m : Type u_2} {α : Type u_11} [inst : AddZeroClass α] (i : m),   (Pi.ev
alAddMonoidHom (fun i => α) i).comp (Matrix.diagAddMonoidHom m α) = Matrix.entry
AddMonoidHom α i i
参数：i : m；Pi.evalAddMonoidHom (fun i => α) i；Matrix.diagAddMonoidHom m α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.evalAddMonoidHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : 
I) → AddZeroClass (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalAddMonoidHom f i
) g = g i
· 使用定理 `Matrix.diagAddMonoidHom_apply`：∀ (n : Type u_3) (α : Type u_11) [inst : 
AddZeroClass α] (A : Matrix n n α) (i : n),   (Matrix.diagAddMonoidHom n α) A i 
= A.diag i
· 使用定理 `Matrix.entryAddMonoidHom_apply`：∀ {m : Type u_2} {n : Type u_3} (α : Typ
e u_11) [inst : AddZeroClass α] (i : m) (j : n) (M : Matrix m n α),   (Matrix.en
tryAddMonoidHom α i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma evalAddMonoidHom_comp_diagAddMonoidHom (i : m) :
    (Pi.evalAddMonoidHom _ i).comp (diagAddMonoidHom m α) = entryAddMonoidHom α i i := by
  simp [AddMonoidHom.ext_iff]
/-
**Matrix.entryAddMonoidHom_toAddHom** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type u_11} [inst : AddZeroClass α] {i
 : m} {j : n},   ↑(Matrix.entryAddMonoidHom α i j) = Matrix.entryAddHom α i j
参数：Matrix.entryAddMonoidHom α i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
@[simp] lemma entryAddMonoidHom_toAddHom {i : m} {j : n} :
    (entryAddMonoidHom α i j : AddHom _ _) = entryAddHom α i j := rfl

end AddMonoidHom

section LinearMap

variable [Semiring R] [AddCommMonoid α] [Module R α]

variable (R α) in
/--
Extracting entries from a matrix as a linear map. Note this cannot be upgraded to an algebra
homomorphism, as it does not respect multiplication.
-/
@[simps]
/-
**Matrix.entryLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：entryLinearMap (i : m) (j : n) : Matrix m n α ->ₗ[R] α where toFun M
参数：i : m；j : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extracting entries from a matrix as a linear map. Note this cannot be upgraded t
o an algebra
homomorphism, as it does not respect multiplication.
-/
def entryLinearMap (i : m) (j : n) :
    Matrix m n α →ₗ[R] α where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
/-
**Matrix.entryLinearMap_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：entryLinearMap_eq_comp {i : m} {j : n} : entryLinearMap R α i j = LinearMa
p.proj j ∘ₗ LinearMap.proj i ∘ₗ (ofLinearEquiv R).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma entryLinearMap_eq_comp {i : m} {j : n} :
    entryLinearMap R α i j =
      LinearMap.proj j ∘ₗ LinearMap.proj i ∘ₗ (ofLinearEquiv R).symm.toLinearMap := by
  rfl
/-
**Matrix.proj_comp_diagLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {R : Type u_7} {α : Type u_11} [inst : Semiring R] [inst_
1 : AddCommMonoid α]   [inst_2 : _root_.Module R α] (i : m), LinearMap.proj i ∘ₗ
 Matrix.diagLinearMap m R α = Matrix.entryLinearMap R α i i
参数：i : m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagLinearMap_apply`：∀ (n : Type u_3) (R : Type u_7) (α : Type u_
11) [inst : Semiring R] [inst_1 : AddCommMonoid α]   [inst_2 : _root_.Module R α
] (a : Matrix n …
· 使用定理 `Matrix.diagAddMonoidHom_apply`：∀ (n : Type u_3) (α : Type u_11) [inst : 
AddZeroClass α] (A : Matrix n n α) (i : n),   (Matrix.diagAddMonoidHom n α) A i 
= A.diag i
· 使用定理 `Matrix.entryLinearMap_apply`：∀ {m : Type u_2} {n : Type u_3} (R : Type u
_7) (α : Type u_11) [inst : Semiring R] [inst_1 : AddCommMonoid α]   [inst_2 : _
root_.Module R α]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma proj_comp_diagLinearMap (i : m) :
    LinearMap.proj i ∘ₗ diagLinearMap m R α = entryLinearMap R α i i := by
  simp [LinearMap.ext_iff]
/-
**Matrix.entryLinearMap_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {R : Type u_7} {α : Type u_11} [inst : Sem
iring R] [inst_1 : AddCommMonoid α]   [inst_2 : _root_.Module R α] {i : m} {j : 
n}, ↑(Matrix.entryLinearMap R α i j) = Matrix.entryAddMonoidHom α i j
参数：Matrix.entryLinearMap R α i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
@[simp] lemma entryLinearMap_toAddMonoidHom {i : m} {j : n} :
    (entryLinearMap R α i j : _ →+ _) = entryAddMonoidHom α i j := rfl
/-
**Matrix.entryLinearMap_toAddHom** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {R : Type u_7} {α : Type u_11} [inst : Sem
iring R] [inst_1 : AddCommMonoid α]   [inst_2 : _root_.Module R α] {i : m} {j : 
n}, ↑(Matrix.entryLinearMap R α i j) = Matrix.entryAddHom α i j
参数：Matrix.entryLinearMap R α i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
@[simp] lemma entryLinearMap_toAddHom {i : m} {j : n} :
    (entryLinearMap R α i j : AddHom _ _) = entryAddHom α i j := rfl

end LinearMap

end Matrix

/-!
### Bundled versions of `Matrix.map`
-/


namespace Equiv

/-- The `Equiv` between spaces of matrices induced by an `Equiv` between their
coefficients. This is `Matrix.map` as an `Equiv`. -/
@[simps apply]
/-
**Equiv.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：mapMatrix (f : α ≃ β) : Matrix m n α ≃ Matrix m n β where toFun M
参数：f : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The `Equiv` between spaces of matrices induced by an `Equiv` between their
coefficients. This is `Matrix.map` as an `Equiv`.
-/
def mapMatrix (f : α ≃ β) : Matrix m n α ≃ Matrix m n β where
  toFun M := M.map f
  invFun M := M.map f.symm
  left_inv _ := Matrix.ext fun _ _ => f.symm_apply_apply _
  right_inv _ := Matrix.ext fun _ _ => f.apply_symm_apply _

@[simp]
/-
**Equiv.mapMatrix_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：mapMatrix_refl : (Equiv.refl α).mapMatrix = Equiv.refl (Matrix m n α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem mapMatrix_refl : (Equiv.refl α).mapMatrix = Equiv.refl (Matrix m n α) :=
  rfl

@[simp]
/-
**Equiv.mapMatrix_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：mapMatrix_symm (f : α ≃ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix
 m n β ≃ _)
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mapMatrix_symm (f : α ≃ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ _) :=
  rfl

@[simp]
/-
**Equiv.mapMatrix_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：mapMatrix_trans (f : α ≃ β) (g : β ≃ γ) : f.mapMatrix.trans g.mapMatrix = 
((f.trans g).mapMatrix : Matrix m n α ≃ _)
参数：f : α ≃ β；g : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem mapMatrix_trans (f : α ≃ β) (g : β ≃ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ _) :=
  rfl

end Equiv

namespace AddMonoidHom

section AddZeroClass
variable [AddZeroClass α] [AddZeroClass β] [AddZeroClass γ]

/-- The `AddMonoidHom` between spaces of matrices induced by an `AddMonoidHom` between their
coefficients. This is `Matrix.map` as an `AddMonoidHom`. -/
@[simps]
/-
**AddMonoidHom.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mapMatrix (f : α ->+ β) : Matrix m n α ->+ Matrix m n β where toFun M
参数：f : α ->+ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `AddMonoidHom` between spaces of matrices induced by an `AddMonoidHom` betwe
en their
coefficients. This is `Matrix.map` as an `AddMonoidHom`.
-/
def mapMatrix (f : α →+ β) : Matrix m n α →+ Matrix m n β where
  toFun M := M.map f
  map_zero' := Matrix.map_zero f f.map_zero
  map_add' := Matrix.map_add f f.map_add

@[simp]
/-
**AddMonoidHom.mapMatrix_id** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：mapMatrix_id : (AddMonoidHom.id α).mapMatrix = AddMonoidHom.id (Matrix m n
 α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_id : (AddMonoidHom.id α).mapMatrix = AddMonoidHom.id (Matrix m n α) :=
  rfl

@[simp]
/-
**AddMonoidHom.mapMatrix_comp** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：mapMatrix_comp (f : β ->+ γ) (g : α ->+ β) : f.mapMatrix.comp g.mapMatrix 
= ((f.comp g).mapMatrix : Matrix m n α ->+ _)
参数：f : β ->+ γ；g : α ->+ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_comp (f : β →+ γ) (g : α →+ β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →+ _) :=
  rfl
/-
**AddMonoidHom.entryAddMonoidHom_comp_mapMatrix** 是 Mathlib 中的一个定理，位于命名空间 `AddMo
noidHom`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type u_11} {β : Type u_12} [inst : Ad
dZeroClass α] [inst_1 : AddZeroClass β]   (f : α →+ β) (i : m) (j : n),   (Matri
x.entryAddMonoidHom β i j).comp f.mapMatrix = f.comp (Matrix.entryAddMonoidHom α
 i j)
参数：f : α →+ β；i : m；j : n；Matrix.entryAddMonoidHom β i j；Matrix.entryAddMonoidHo
m α i j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma entryAddMonoidHom_comp_mapMatrix (f : α →+ β) (i : m) (j : n) :
    (entryAddMonoidHom β i j).comp f.mapMatrix = f.comp (entryAddMonoidHom α i j) := rfl

@[simp]
/-
**AddMonoidHom.mapMatrix_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：mapMatrix_zero : (0 : α ->+ β).mapMatrix = (0 : Matrix m n α ->+ _)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_zero : (0 : α →+ β).mapMatrix = (0 : Matrix m n α →+ _) := rfl

end AddZeroClass

@[simp]
/-
**AddMonoidHom.mapMatrix_add** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：mapMatrix_add [AddZeroClass α] [AddCommMonoid β] (f g : α ->+ β) : (f + g)
.mapMatrix = (f.mapMatrix + g.mapMatrix : Matrix m n α ->+ _)
参数：f g : α ->+ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_add [AddZeroClass α] [AddCommMonoid β] (f g : α →+ β) :
    (f + g).mapMatrix = (f.mapMatrix + g.mapMatrix : Matrix m n α →+ _) := rfl

@[simp]
/-
**AddMonoidHom.mapMatrix_sub** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：mapMatrix_sub [AddZeroClass α] [AddCommGroup β] (f g : α ->+ β) : (f - g).
mapMatrix = (f.mapMatrix - g.mapMatrix : Matrix m n α ->+ _)
参数：f g : α ->+ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_sub [AddZeroClass α] [AddCommGroup β] (f g : α →+ β) :
    (f - g).mapMatrix = (f.mapMatrix - g.mapMatrix : Matrix m n α →+ _) := rfl

@[simp]
/-
**AddMonoidHom.mapMatrix_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：mapMatrix_neg [AddZeroClass α] [AddCommGroup β] (f : α ->+ β) : (-f).mapMa
trix = (-f.mapMatrix : Matrix m n α ->+ _)
参数：f : α ->+ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_neg [AddZeroClass α] [AddCommGroup β] (f : α →+ β) :
    (-f).mapMatrix = (-f.mapMatrix : Matrix m n α →+ _) := rfl

@[simp]
/-
**AddMonoidHom.mapMatrix_smul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：mapMatrix_smul [Monoid A] [AddZeroClass α] [AddMonoid β] [DistribMulAction
 A β] (a : A) (f : α ->+ β) : (a • f).mapMatrix = (a • f.mapMatrix : Matrix m n 
α ->+ _)
参数：a : A；f : α ->+ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_smul [Monoid A] [AddZeroClass α] [AddMonoid β] [DistribMulAction A β]
    (a : A) (f : α →+ β) :
    (a • f).mapMatrix = (a • f.mapMatrix : Matrix m n α →+ _) := rfl

end AddMonoidHom

namespace AddEquiv

variable [Add α] [Add β] [Add γ]

/-- The `AddEquiv` between spaces of matrices induced by an `AddEquiv` between their
coefficients. This is `Matrix.map` as an `AddEquiv`. -/
@[simps apply]
/-
**AddEquiv.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `AddEquiv`。
形式化陈述：mapMatrix (f : α ≃+ β) : Matrix m n α ≃+ Matrix m n β
参数：f : α ≃+ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `AddEquiv` between spaces of matrices induced by an `AddEquiv` between their
coefficients. This is `Matrix.map` as an `AddEquiv`.
-/
def mapMatrix (f : α ≃+ β) : Matrix m n α ≃+ Matrix m n β :=
  { f.toEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm
    map_add' := Matrix.map_add f (map_add f) }

@[simp]
/-
**AddEquiv.mapMatrix_refl** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：mapMatrix_refl : (AddEquiv.refl α).mapMatrix = AddEquiv.refl (Matrix m n α
)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_refl : (AddEquiv.refl α).mapMatrix = AddEquiv.refl (Matrix m n α) :=
  rfl

@[simp]
/-
**AddEquiv.mapMatrix_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：mapMatrix_symm (f : α ≃+ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matri
x m n β ≃+ _)
参数：f : α ≃+ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_symm (f : α ≃+ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃+ _) :=
  rfl

@[simp]
/-
**AddEquiv.mapMatrix_trans** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：mapMatrix_trans (f : α ≃+ β) (g : β ≃+ γ) : f.mapMatrix.trans g.mapMatrix 
= ((f.trans g).mapMatrix : Matrix m n α ≃+ _)
参数：f : α ≃+ β；g : β ≃+ γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_trans (f : α ≃+ β) (g : β ≃+ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃+ _) :=
  rfl
/-
**AddEquiv.entryAddHom_comp_mapMatrix** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type u_11} {β : Type u_12} [inst : Ad
d α] [inst_1 : Add β] (f : α ≃+ β) (i : m)   (j : n), (Matrix.entryAddHom β i j)
.comp ↑f.mapMatrix = (↑f).comp (Matrix.entryAddHom α i j)
参数：f : α ≃+ β；i : m；j : n；Matrix.entryAddHom β i j；↑f；Matrix.entryAddHom α i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquivClass.instAddHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Add M] [inst_1 : Add N] [inst_2 : EquivLike F M N]   [h : AddEquiv
Class F M N], AddHo…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
@[simp] lemma entryAddHom_comp_mapMatrix (f : α ≃+ β) (i : m) (j : n) :
    (entryAddHom β i j).comp (AddHomClass.toAddHom f.mapMatrix) =
      (f : AddHom α β).comp (entryAddHom _ i j) := rfl

end AddEquiv

namespace LinearMap

variable [Semiring R] [Semiring S] [Semiring T]
variable {σᵣₛ : R →+* S} {σₛₜ : S →+* T} {σᵣₜ : R →+* T} [RingHomCompTriple σᵣₛ σₛₜ σᵣₜ]

section AddCommMonoid
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module S β] [Module T γ]

/-- The `LinearMap` between spaces of matrices induced by a `LinearMap` between their
coefficients. This is `Matrix.map` as a `LinearMap`. -/
@[simps]
/-
**LinearMap.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：mapMatrix (f : α ->ₛₗ[σᵣₛ] β) : Matrix m n α ->ₛₗ[σᵣₛ] Matrix m n β where 
toFun M
参数：f : α ->ₛₗ[σᵣₛ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `LinearMap` between spaces of matrices induced by a `LinearMap` between thei
r
coefficients. This is `Matrix.map` as a `LinearMap`.
-/
def mapMatrix (f : α →ₛₗ[σᵣₛ] β) : Matrix m n α →ₛₗ[σᵣₛ] Matrix m n β where
  toFun M := M.map f
  map_add' := Matrix.map_add f f.map_add
  map_smul' r := Matrix.map_smulₛₗ f _ r (f.map_smulₛₗ r)

@[simp]
/-
**LinearMap.mapMatrix_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrix_id : LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α ->ₗ[R
] _)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_id : LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α →ₗ[R] _) :=
  rfl

@[simp]
/-
**LinearMap.mapMatrix_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrix_comp (f : β ->ₛₗ[σₛₜ] γ) (g : α ->ₛₗ[σᵣₛ] β) : f.mapMatrix.comp 
g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α ->ₛₗ[_] _)
参数：f : β ->ₛₗ[σₛₜ] γ；g : α ->ₛₗ[σᵣₛ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_comp (f : β →ₛₗ[σₛₜ] γ) (g : α →ₛₗ[σᵣₛ] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →ₛₗ[_] _) :=
  rfl
/-
**LinearMap.entryLinearMap_comp_mapMatrix** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {R : Type u_7} {S : Type u_8} {α : Type u_
11} {β : Type u_12} [inst : Semiring R]   [inst_1 : Semiring S] {σᵣₛ : R →+* S} 
[inst_2 : AddCommMonoid α] [inst_3 : AddCommMonoid β]   [inst_4 : _root_.Module 
R α] [inst_5 : _root_.Module S β] (f : α →ₛₗ[σᵣₛ] β) (i : m) (j : n),   Matrix.e
ntryLinearMap S β i j ∘ₛₗ f.mapMatrix = f ∘ₛₗ Matrix.entryLinearMap R α i j
参数：f : α →ₛₗ[σᵣₛ] β；i : m；j : n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma entryLinearMap_comp_mapMatrix (f : α →ₛₗ[σᵣₛ] β) (i : m) (j : n) :
    (entryLinearMap S _ i j).comp f.mapMatrix = f.comp (entryLinearMap R _ i j) := rfl

@[simp]
/-
**LinearMap.mapMatrix_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrix_zero : (0 : α ->ₛₗ[σᵣₛ] β).mapMatrix = (0 : Matrix m n α ->ₛₗ[_]
 _)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_zero : (0 : α →ₛₗ[σᵣₛ] β).mapMatrix = (0 : Matrix m n α →ₛₗ[_] _) := rfl

@[simp]
/-
**LinearMap.mapMatrix_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrix_add (f g : α ->ₛₗ[σᵣₛ] β) : (f + g).mapMatrix = (f.mapMatrix + g
.mapMatrix : Matrix m n α ->ₛₗ[_] _)
参数：f g : α ->ₛₗ[σᵣₛ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_add (f g : α →ₛₗ[σᵣₛ] β) :
    (f + g).mapMatrix = (f.mapMatrix + g.mapMatrix : Matrix m n α →ₛₗ[_] _) := rfl

@[simp]
/-
**LinearMap.mapMatrix_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrix_smul [Monoid A] [DistribMulAction A β] [SMulCommClass S A β] (a 
: A) (f : α ->ₛₗ[σᵣₛ] β) : (a • f).mapMatrix = (a • f.mapMatrix : Matrix m n α -
>ₛₗ[_] _)
参数：a : A；f : α ->ₛₗ[σᵣₛ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_smul [Monoid A] [DistribMulAction A β] [SMulCommClass S A β]
    (a : A) (f : α →ₛₗ[σᵣₛ] β) :
    (a • f).mapMatrix = (a • f.mapMatrix : Matrix m n α →ₛₗ[_] _) := rfl

variable (A) in
/-- `LinearMap.mapMatrix` is itself linear in the map being applied.

Alternative, this is `Matrix.map` as a bilinear map. -/
@[simps]
/-
**LinearMap.mapMatrixLinear** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：mapMatrixLinear [Semiring A] [Module A β] [SMulCommClass S A β] : (α ->ₛₗ[
σᵣₛ] β) ->ₗ[A] (Matrix m n α ->ₛₗ[σᵣₛ] Matrix m n β) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mapMatrix_add`：mapMatrix_add (f g : α ->ₛₗ[σᵣₛ] β) : (f + g).m
apMatrix = (f.mapMatrix + g.mapMatrix : Matrix m n α ->ₛₗ[_] _)

--- 原说明 ---
`LinearMap.mapMatrix` is itself linear in the map being applied.

Alternative, this is `Matrix.map` as a bilinear map.
-/
def mapMatrixLinear [Semiring A] [Module A β] [SMulCommClass S A β] :
    (α →ₛₗ[σᵣₛ] β) →ₗ[A] (Matrix m n α →ₛₗ[σᵣₛ] Matrix m n β) where
  toFun := mapMatrix
  map_add' := mapMatrix_add
  map_smul' := mapMatrix_smul

end AddCommMonoid

section
variable [AddCommMonoid α] [AddCommGroup β]
variable [Module R α] [Module S β]

@[simp]
/-
**LinearMap.mapMatrix_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrix_sub (f g : α ->ₛₗ[σᵣₛ] β) : (f - g).mapMatrix = (f.mapMatrix - g
.mapMatrix : Matrix m n α ->ₛₗ[σᵣₛ] _)
参数：f g : α ->ₛₗ[σᵣₛ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_sub (f g : α →ₛₗ[σᵣₛ] β) :
    (f - g).mapMatrix = (f.mapMatrix - g.mapMatrix : Matrix m n α →ₛₗ[σᵣₛ] _) := rfl

@[simp]
/-
**LinearMap.mapMatrix_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrix_neg (f : α ->ₛₗ[σᵣₛ] β) : (-f).mapMatrix = (-f.mapMatrix : Matri
x m n α ->ₛₗ[σᵣₛ] _)
参数：f : α ->ₛₗ[σᵣₛ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_neg (f : α →ₛₗ[σᵣₛ] β) :
    (-f).mapMatrix = (-f.mapMatrix : Matrix m n α →ₛₗ[σᵣₛ] _) := rfl

end

end LinearMap

namespace LinearEquiv

variable [Semiring R] [Semiring S] [Semiring T]
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module S β] [Module T γ]
variable {σᵣₛ : R →+* S} {σₛₜ : S →+* T} {σᵣₜ : R →+* T} [RingHomCompTriple σᵣₛ σₛₜ σᵣₜ]
variable {σₛᵣ : S →+* R} {σₜₛ : T →+* S} {σₜᵣ : T →+* R} [RingHomCompTriple σₜₛ σₛᵣ σₜᵣ]
variable [RingHomInvPair σᵣₛ σₛᵣ] [RingHomInvPair σₛᵣ σᵣₛ]
variable [RingHomInvPair σₛₜ σₜₛ] [RingHomInvPair σₜₛ σₛₜ]
variable [RingHomInvPair σᵣₜ σₜᵣ] [RingHomInvPair σₜᵣ σᵣₜ]

/-- The `LinearEquiv` between spaces of matrices induced by a `LinearEquiv` between their
coefficients. This is `Matrix.map` as a `LinearEquiv`. -/
@[simps apply]
/-
**LinearEquiv.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：mapMatrix (f : α ≃ₛₗ[σᵣₛ] β) : Matrix m n α ≃ₛₗ[σᵣₛ] Matrix m n β
参数：f : α ≃ₛₗ[σᵣₛ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `LinearEquiv` between spaces of matrices induced by a `LinearEquiv` between 
their
coefficients. This is `Matrix.map` as a `LinearEquiv`.
-/
def mapMatrix (f : α ≃ₛₗ[σᵣₛ] β) : Matrix m n α ≃ₛₗ[σᵣₛ] Matrix m n β :=
  { f.toEquiv.mapMatrix,
    f.toLinearMap.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
/-
**LinearEquiv.mapMatrix_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：mapMatrix_refl : (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Ma
trix m n α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_refl : (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Matrix m n α) :=
  rfl

@[simp]
/-
**LinearEquiv.mapMatrix_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：mapMatrix_symm (f : α ≃ₛₗ[σᵣₛ] β) : f.mapMatrix.symm = (f.symm.mapMatrix :
 Matrix m n β ≃ₛₗ[_] _)
参数：f : α ≃ₛₗ[σᵣₛ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_symm (f : α ≃ₛₗ[σᵣₛ] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ₛₗ[_] _) :=
  rfl

@[simp]
/-
**LinearEquiv.mapMatrix_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：mapMatrix_trans (f : α ≃ₛₗ[σᵣₛ] β) (g : β ≃ₛₗ[σₛₜ] γ) : f.mapMatrix.trans 
g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ₛₗ[_] _)
参数：f : α ≃ₛₗ[σᵣₛ] β；g : β ≃ₛₗ[σₛₜ] γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_trans (f : α ≃ₛₗ[σᵣₛ] β) (g : β ≃ₛₗ[σₛₜ] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ₛₗ[_] _) :=
  rfl
/-
**LinearEquiv.mapMatrix_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {R : Type u_7} {S : Type u_8} {α : Type u_
11} {β : Type u_12} [inst : Semiring R]   [inst_1 : Semiring S] [inst_2 : AddCom
mMonoid α] [inst_3 : AddCommMonoid β] [inst_4 : _root_.Module R α]   [inst_5 : _
root_.Module S β] {σᵣₛ : R →+* S} {σₛᵣ : S →+* R} [inst_6 : RingHomInvPair σᵣₛ σ
ₛᵣ]   [inst_7 : RingHomInvPair σₛᵣ σᵣₛ] (f : α ≃ₛₗ[σᵣₛ] β), ↑f.mapMatrix = (↑f).
mapMatrix
参数：f : α ≃ₛₗ[σᵣₛ] β；↑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapMatrix_toLinearMap (f : α ≃ₛₗ[σᵣₛ] β) :
    (f.mapMatrix : _ ≃ₛₗ[_] Matrix m n β).toLinearMap = f.toLinearMap.mapMatrix := by
  rfl
/-
**LinearEquiv.entryLinearMap_comp_mapMatrix** 是 Mathlib 中的一个引理，位于命名空间 `LinearEqu
iv`。
形式化陈述：entryLinearMap_comp_mapMatrix (f : α ≃ₛₗ[σᵣₛ] β) (i : m) (j : n) : (entryL
inearMap S _ i j).comp f.mapMatrix.toLinearMap = f.toLinearMap.comp (entryLinear
Map R _ i j)
参数：f : α ≃ₛₗ[σᵣₛ] β；i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.mapMatrix_toLinearMap`：∀ {m : Type u_2} {n : Type u_3} {R : 
Type u_7} {S : Type u_8} {α : Type u_11} {β : Type u_12} [inst : Semiring R]   [
inst_1 : Semiring S] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma entryLinearMap_comp_mapMatrix (f : α ≃ₛₗ[σᵣₛ] β) (i : m) (j : n) :
    (entryLinearMap S _ i j).comp f.mapMatrix.toLinearMap =
      f.toLinearMap.comp (entryLinearMap R _ i j) := by
  simp only [mapMatrix_toLinearMap, LinearMap.entryLinearMap_comp_mapMatrix]

end LinearEquiv

namespace RingHom

variable [Fintype m] [DecidableEq m]
variable [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]

/-- The `RingHom` between spaces of square matrices induced by a `RingHom` between their
coefficients. This is `Matrix.map` as a `RingHom`. -/
@[simps]
/-
**RingHom.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：mapMatrix (f : α ->+* β) : Matrix m m α ->+* Matrix m m β
参数：f : α ->+* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `RingHom` between spaces of square matrices induced by a `RingHom` between t
heir
coefficients. This is `Matrix.map` as a `RingHom`.
-/
def mapMatrix (f : α →+* β) : Matrix m m α →+* Matrix m m β :=
  { f.toAddMonoidHom.mapMatrix with
    toFun := fun M => M.map f
    map_one' := by simp
    map_mul' := fun _ _ => Matrix.map_mul }

@[simp]
/-
**RingHom.mapMatrix_id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mapMatrix_id : (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_id : (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α) :=
  rfl

@[simp]
/-
**RingHom.mapMatrix_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mapMatrix_comp (f : β ->+* γ) (g : α ->+* β) : f.mapMatrix.comp g.mapMatri
x = ((f.comp g).mapMatrix : Matrix m m α ->+* _)
参数：f : β ->+* γ；g : α ->+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_comp (f : β →+* γ) (g : α →+* β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →+* _) :=
  rfl
/-
**RingHom._root_.Matrix.map_pow** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.Matrix.map_pow {α β : Type*} [Semiring α] [Semiring β]
    (M : Matrix m m α) (f : α →+* β) (a : ℕ) : (M ^ a).map f = (M.map f) ^ a :=
  f.mapMatrix.map_pow M a

end RingHom

namespace RingEquiv

variable [Fintype m] [DecidableEq m]
variable [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]

/-- The `RingEquiv` between spaces of square matrices induced by a `RingEquiv` between their
coefficients. This is `Matrix.map` as a `RingEquiv`. -/
@[simps apply]
/-
**RingEquiv.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：mapMatrix (f : α ≃+* β) : Matrix m m α ≃+* Matrix m m β
参数：f : α ≃+* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `RingEquiv` between spaces of square matrices induced by a `RingEquiv` betwe
en their
coefficients. This is `Matrix.map` as a `RingEquiv`.
-/
def mapMatrix (f : α ≃+* β) : Matrix m m α ≃+* Matrix m m β :=
  { f.toRingHom.mapMatrix,
    f.toAddEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
/-
**RingEquiv.mapMatrix_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：mapMatrix_refl : (RingEquiv.refl α).mapMatrix = RingEquiv.refl (Matrix m m
 α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_refl : (RingEquiv.refl α).mapMatrix = RingEquiv.refl (Matrix m m α) :=
  rfl

@[simp]
/-
**RingEquiv.mapMatrix_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：mapMatrix_symm (f : α ≃+* β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matr
ix m m β ≃+* _)
参数：f : α ≃+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_symm (f : α ≃+* β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃+* _) :=
  rfl

@[simp]
/-
**RingEquiv.mapMatrix_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：mapMatrix_trans (f : α ≃+* β) (g : β ≃+* γ) : f.mapMatrix.trans g.mapMatri
x = ((f.trans g).mapMatrix : Matrix m m α ≃+* _)
参数：f : α ≃+* β；g : β ≃+* γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_trans (f : α ≃+* β) (g : β ≃+* γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃+* _) :=
  rfl

open MulOpposite in
/-- For any ring `α`, we have ring isomorphism `Matₙₓₙ(αᵒᵖ) ≅ (Matₙₓₙ(α))ᵒᵖ` given by transpose.

See also `Matrix.transposeRingEquiv` for a version that doesn't take the opposite of `α`,
given that its multiplication is commutative. -/
@[simps apply symm_apply]
/-
**RingEquiv.mopMatrix** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：mopMatrix {α} [Mul α] [AddCommMonoid α] : Matrix m m αᵐᵒᵖ ≃+* (Matrix m m 
α)ᵐᵒᵖ where toFun M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any ring `α`, we have ring isomorphism `Matₙₓₙ(αᵒᵖ) ≅ (Matₙₓₙ(α))ᵒᵖ` given b
y transpose.

See also `Matrix.transposeRingEquiv` for a version that doesn't take the opposit
e of `α`,
given that its multiplication is commutative.
-/
def mopMatrix {α} [Mul α] [AddCommMonoid α] : Matrix m m αᵐᵒᵖ ≃+* (Matrix m m α)ᵐᵒᵖ where
  toFun M := op (M.transpose.map unop)
  invFun M := M.unop.transpose.map op
  map_mul' _ _ := unop_injective <| by ext; simp [mul_apply]
  map_add' _ _ := rfl

end RingEquiv

set_option backward.isDefEq.respectTransparency false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α) [MulOne α] [AddCommMonoid α] [IsStablyFiniteRing α] : IsStablyFiniteRing αᵐᵒᵖ where
  isDedekindFiniteMonoid n := .of_injective (MonoidHom.mk
    ⟨RingEquiv.mopMatrix, by simp⟩ RingEquiv.mopMatrix.map_mul) (RingEquiv.injective _)

open MulOpposite in
/-
**MulOpposite.isStablyFiniteRing_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulOpposite.isStablyFiniteRing_iff (α) [MulOne α] [AddCommMonoid α] : IsSt
ablyFiniteRing αᵐᵒᵖ ↔ IsStablyFiniteRing α where mp _
参数：α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Finset.op_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] 
(s : Finset ι) (f : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposi
te.…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsDedekindFiniteMonoid.of_injective`：∀ {M : Type u_4} {N : Type u_5} {F 
: Type u_9} [inst : MulOne M] [inst_1 : MulOne N] [inst_2 : FunLike F M N]   [Mo
noidHomClass F M N] (f : …
· 使用定理 `Matrix.map_injective`：map_injective {f : α -> β} (hf : Function.Injectiv
e f) : Function.Injective fun M : Matrix m n α => M.map f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `IsStablyFiniteRing.isDedekindFiniteMonoid`：∀ {R : Type u_10} {inst : Mul
One R} {inst_1 : AddCommMonoid R} [self : IsStablyFiniteRing R] (n : ℕ),   IsDed
ekindFiniteMonoid (Matrix (Fin …
· 使用定理 `instIsStablyFiniteRingMulOpposite`：∀ (α : Type u_14) [inst : MulOne α] [
inst_1 : AddCommMonoid α] [IsStablyFiniteRing α], IsStablyFiniteRing αᵐᵒᵖ
-/
theorem MulOpposite.isStablyFiniteRing_iff (α) [MulOne α] [AddCommMonoid α] :
    IsStablyFiniteRing αᵐᵒᵖ ↔ IsStablyFiniteRing α where
  mp _ :=
  ⟨fun n ↦ let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) α ↦ M.map (op ∘ op), by aesop⟩
               fun _ _ ↦ by ext; simp [mul_apply]
  .of_injective f (map_injective (op_injective.comp op_injective))⟩
  mpr _ := inferInstance

namespace AlgHom

variable [Fintype m] [DecidableEq m]
variable [CommSemiring R] [Semiring α] [Semiring β] [Semiring γ]
variable [Algebra R α] [Algebra R β] [Algebra R γ]

/-- The `AlgHom` between spaces of square matrices induced by an `AlgHom` between their
coefficients. This is `Matrix.map` as an `AlgHom`. -/
@[simps]
/-
**AlgHom.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：mapMatrix (f : α ->ₐ[R] β) : Matrix m m α ->ₐ[R] Matrix m m β
参数：f : α ->ₐ[R] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `AlgHom` between spaces of square matrices induced by an `AlgHom` between th
eir
coefficients. This is `Matrix.map` as an `AlgHom`.
-/
def mapMatrix (f : α →ₐ[R] β) : Matrix m m α →ₐ[R] Matrix m m β :=
  { f.toRingHom.mapMatrix with
    toFun := fun M => M.map f
    commutes' := fun r => Matrix.map_algebraMap r f (map_zero _) (f.commutes r) }

@[simp]
/-
**AlgHom.mapMatrix_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mapMatrix_id : (AlgHom.id R α).mapMatrix = AlgHom.id R (Matrix m m α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_id : (AlgHom.id R α).mapMatrix = AlgHom.id R (Matrix m m α) :=
  rfl

@[simp]
/-
**AlgHom.mapMatrix_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mapMatrix_comp (f : β ->ₐ[R] γ) (g : α ->ₐ[R] β) : f.mapMatrix.comp g.mapM
atrix = ((f.comp g).mapMatrix : Matrix m m α ->ₐ[R] _)
参数：f : β ->ₐ[R] γ；g : α ->ₐ[R] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_comp (f : β →ₐ[R] γ) (g : α →ₐ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →ₐ[R] _) :=
  rfl

end AlgHom

namespace AlgEquiv

variable [Fintype m] [DecidableEq m]
variable [CommSemiring R] [Semiring α] [Semiring β] [Semiring γ]
variable [Algebra R α] [Algebra R β] [Algebra R γ]

/-- The `AlgEquiv` between spaces of square matrices induced by an `AlgEquiv` between their
coefficients. This is `Matrix.map` as an `AlgEquiv`. -/
@[simps apply]
/-
**AlgEquiv.mapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：mapMatrix (f : α ≃ₐ[R] β) : Matrix m m α ≃ₐ[R] Matrix m m β
参数：f : α ≃ₐ[R] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `AlgEquiv` between spaces of square matrices induced by an `AlgEquiv` betwee
n their
coefficients. This is `Matrix.map` as an `AlgEquiv`.
-/
def mapMatrix (f : α ≃ₐ[R] β) : Matrix m m α ≃ₐ[R] Matrix m m β :=
  { f.toAlgHom.mapMatrix,
    f.toRingEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
/-
**AlgEquiv.mapMatrix_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：mapMatrix_refl : AlgEquiv.refl.mapMatrix = (AlgEquiv.refl : Matrix m m α ≃
ₐ[R] _)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_refl : AlgEquiv.refl.mapMatrix = (AlgEquiv.refl : Matrix m m α ≃ₐ[R] _) :=
  rfl

@[simp]
/-
**AlgEquiv.mapMatrix_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：mapMatrix_symm (f : α ≃ₐ[R] β) : f.mapMatrix.symm = (f.symm.mapMatrix : Ma
trix m m β ≃ₐ[R] _)
参数：f : α ≃ₐ[R] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_symm (f : α ≃ₐ[R] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃ₐ[R] _) :=
  rfl

@[simp]
/-
**AlgEquiv.mapMatrix_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：mapMatrix_trans (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ) : f.mapMatrix.trans g.mapM
atrix = ((f.trans g).mapMatrix : Matrix m m α ≃ₐ[R] _)
参数：f : α ≃ₐ[R] β；g : β ≃ₐ[R] γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMatrix_trans (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃ₐ[R] _) :=
  rfl

/-- For any algebra `α` over a ring `R`, we have an `R`-algebra isomorphism
`Matₙₓₙ(αᵒᵖ) ≅ (Matₙₓₙ(R))ᵒᵖ` given by transpose.

See also `Matrix.transposeAlgEquiv` for a version that doesn't take the opposite of `α`,
given that its multiplication is commutative. -/
/-
**AlgEquiv.mopMatrix** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：{m : Type u_2} →   {R : Type u_7} →     {α : Type u_11} →       [inst : Fi
ntype m] →         [inst_1 : DecidableEq m] →           [inst_2 : CommSemiring R
] →             [inst_3 : Semiring α] → [inst_4 : Algebra R α] → Matrix m m αᵐᵒᵖ
 ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ
参数：Matrix m m α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any algebra `α` over a ring `R`, we have an `R`-algebra isomorphism
`Matₙₓₙ(αᵒᵖ) ≅ (Matₙₓₙ(R))ᵒᵖ` given by transpose.

See also `Matrix.transposeAlgEquiv` for a version that doesn't take the opposite
 of `α`,
given that its multiplication is commutative.
-/
@[simps!] def mopMatrix : Matrix m m αᵐᵒᵖ ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ where
  __ := RingEquiv.mopMatrix
  commutes' _ := MulOpposite.unop_injective <| by
    ext; simp [algebraMap_matrix_apply, eq_comm, apply_ite MulOpposite.unop]

end AlgEquiv

namespace AddSubmonoid

variable {A : Type*} [AddMonoid A]

/-- A version of `Set.matrix` for `AddSubmonoid`s.
Given an `AddSubmonoid` `S`, `S.matrix` is the `AddSubmonoid` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps]
/-
**AddSubmonoid.matrix** 是 Mathlib 中的一个定义，位于命名空间 `AddSubmonoid`。
形式化陈述：matrix (S : AddSubmonoid A) : AddSubmonoid (Matrix m n A) where carrier
参数：S : AddSubmonoid A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.matrix` for `AddSubmonoid`s.
Given an `AddSubmonoid` `S`, `S.matrix` is the `AddSubmonoid` of matrices `m`
all of whose entries `m i j` belong to `S`.
-/
def matrix (S : AddSubmonoid A) : AddSubmonoid (Matrix m n A) where
  carrier := Set.matrix S
  add_mem' hm hn i j := add_mem (hm i j) (hn i j)
  zero_mem' _ _ := zero_mem _

end AddSubmonoid

namespace AddSubgroup

variable {A : Type*} [AddGroup A]

/-- A version of `Set.matrix` for `AddSubgroup`s.
Given an `AddSubgroup` `S`, `S.matrix` is the `AddSubgroup` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/-
**AddSubgroup.matrix** 是 Mathlib 中的一个定义，位于命名空间 `AddSubgroup`。
形式化陈述：matrix (S : AddSubgroup A) : AddSubgroup (Matrix m n A) where __
参数：S : AddSubgroup A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.matrix` for `AddSubgroup`s.
Given an `AddSubgroup` `S`, `S.matrix` is the `AddSubgroup` of matrices `m`
all of whose entries `m i j` belong to `S`.
-/
def matrix (S : AddSubgroup A) : AddSubgroup (Matrix m n A) where
  __ := S.toAddSubmonoid.matrix
  neg_mem' hm i j := AddSubgroup.neg_mem _ (hm i j)

end AddSubgroup

namespace Subsemiring

variable {R : Type*} [NonAssocSemiring R]
variable [Fintype n] [DecidableEq n]

/-- A version of `Set.matrix` for `Subsemiring`s.
Given a `Subsemiring` `S`, `S.matrix` is the `Subsemiring` of square matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/-
**Subsemiring.matrix** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：matrix (S : Subsemiring R) : Subsemiring (Matrix n n R) where __
参数：S : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.matrix` for `Subsemiring`s.
Given a `Subsemiring` `S`, `S.matrix` is the `Subsemiring` of square matrices `m
`
all of whose entries `m i j` belong to `S`.
-/
def matrix (S : Subsemiring R) : Subsemiring (Matrix n n R) where
  __ := S.toAddSubmonoid.matrix
  mul_mem' ha hb i j := Subsemiring.sum_mem _ (fun k _ => Subsemiring.mul_mem _ (ha i k) (hb k j))
  one_mem' := (diagonal_mem_matrix_iff (Subsemiring.zero_mem _)).mpr fun _ => Subsemiring.one_mem _

end Subsemiring

namespace Subring

variable {R : Type*} [NonAssocRing R]
variable [Fintype n] [DecidableEq n]

/-- A version of `Set.matrix` for `Subring`s.
Given a `Subring` `S`, `S.matrix` is the `Subring` of square matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/-
**Subring.matrix** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：matrix (S : Subring R) : Subring (Matrix n n R) where __
参数：S : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.matrix` for `Subring`s.
Given a `Subring` `S`, `S.matrix` is the `Subring` of square matrices `m`
all of whose entries `m i j` belong to `S`.
-/
def matrix (S : Subring R) : Subring (Matrix n n R) where
  __ := S.toSubsemiring.matrix
  neg_mem' hm i j := Subring.neg_mem _ (hm i j)

end Subring

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A version of `Set.matrix` for `Submodule`s.
Given a `Submodule` `S`, `S.matrix` is the `Submodule` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/-
**Submodule.matrix** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：matrix (S : Submodule R M) : Submodule R (Matrix m n M) where __
参数：S : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.matrix` for `Submodule`s.
Given a `Submodule` `S`, `S.matrix` is the `Submodule` of matrices `m`
all of whose entries `m i j` belong to `S`.
-/
def matrix (S : Submodule R M) : Submodule R (Matrix m n M) where
  __ := S.toAddSubmonoid.matrix
  smul_mem' _ _ hm i j := Submodule.smul_mem _ _ (hm i j)

end Submodule

open Matrix

namespace Matrix

section Pi

variable {ι : Type*} {β : ι → Type*}

/-- Matrices over a Pi type are in canonical bijection with tuples of matrices. -/
/-
**Matrix.piEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} → {ι : Type u_14} → {β : ι → Type u_15} 
→ Matrix m n ((i : ι) → β i) ≃ ((i : ι) → Matrix m n (β i))
参数：(i : ι) → β i；(i : ι) → Matrix m n (β i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Matrices over a Pi type are in canonical bijection with tuples of matrices.
-/
@[simps] def piEquiv : Matrix m n (Π i, β i) ≃ Π i, Matrix m n (β i) where
  toFun f i := f.map (· i)
  invFun f := .of fun j k i ↦ f i j k
  left_inv _ := rfl
  right_inv _ := rfl

/-- `piEquiv` as an `AddEquiv`. -/
/-
**Matrix.piAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} →     {ι : Type u_14} →       {β : ι → T
ype u_15} → [inst : (i : ι) → Add (β i)] → Matrix m n ((i : ι) → β i) ≃+ ((i : ι
) → Matrix m n (β i))
参数：i : ι；β i；(i : ι) → β i；(i : ι) → Matrix m n (β i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`piEquiv` as an `AddEquiv`.
-/
@[simps!] def piAddEquiv [∀ i, Add (β i)] : Matrix m n (Π i, β i) ≃+ Π i, Matrix m n (β i) where
  __ := piEquiv
  map_add' _ _ := rfl

/-- `piEquiv` as a `LinearEquiv`. -/
/-
**Matrix.piLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} →     {ι : Type u_14} →       {β : ι → T
ype u_15} →         (R : Type u_16) →           [inst : Semiring R] →           
  [inst_1 : (i : ι) → AddCommMonoid (β i)] →               [inst_2 : (i : ι) → _
root_.Module R (β i)] → Matrix m n ((i : ι) → β i) ≃ₗ[R] (i : ι) → Matrix m n (β
 i)
参数：R : Type u_16；i : ι；β i；i : ι；β i；(i : ι) → β i；i : ι；β i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`piEquiv` as a `LinearEquiv`.
-/
@[simps] def piLinearEquiv (R) [Semiring R] [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] :
    Matrix m n (Π i, β i) ≃ₗ[R] Π i, Matrix m n (β i) where
  __ := piAddEquiv
  map_smul' _ _ := rfl

/-- `piEquiv` as a `RingEquiv`. -/
/-
**Matrix.piRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_3} →   {ι : Type u_14} →     {β : ι → Type u_15} →       [inst
 : (i : ι) → AddCommMonoid (β i)] →         [inst_1 : (i : ι) → Mul (β i)] →    
       [inst_2 : Fintype n] → Matrix n n ((i : ι) → β i) ≃+* ((i : ι) → Matrix n
 n (β i))
参数：i : ι；β i；i : ι；β i；(i : ι) → β i；(i : ι) → Matrix n n (β i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`piEquiv` as a `RingEquiv`.
-/
@[simps!] def piRingEquiv [∀ i, AddCommMonoid (β i)] [∀ i, Mul (β i)] [Fintype n] :
    Matrix n n (Π i, β i) ≃+* Π i, Matrix n n (β i) where
  __ := piAddEquiv
  map_mul' _ _ := by ext; simp [Matrix.mul_apply]

/-- `piEquiv` as an `AlgEquiv`. -/
/-
**Matrix.piAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_3} →   {ι : Type u_14} →     {β : ι → Type u_15} →       (R : 
Type u_16) →         [inst : CommSemiring R] →           [inst_1 : (i : ι) → Sem
iring (β i)] →             [inst_2 : (i : ι) → Algebra R (β i)] →               
[inst_3 : Fintype n] →                 [inst_4 : DecidableEq n] → Matrix n n ((i
 : ι) → β i) ≃ₐ[R] (i : ι) → Matrix n n (β i)
参数：R : Type u_16；i : ι；β i；i : ι；β i；(i : ι) → β i；i : ι；β i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`piEquiv` as an `AlgEquiv`.
-/
@[simps!] def piAlgEquiv (R) [CommSemiring R] [∀ i, Semiring (β i)] [∀ i, Algebra R (β i)]
    [Fintype n] [DecidableEq n] : Matrix n n (Π i, β i) ≃ₐ[R] Π i, Matrix n n (β i) where
  __ := piRingEquiv
  commutes' := (AlgHom.mk' (piRingEquiv (β := β) (n := n)).toRingHom fun _ _ ↦ rfl).commutes

end Pi

section Transpose

open Matrix

variable (m n α)

/-- `Matrix.transpose` as an `AddEquiv` -/
@[simps apply]
/-
**Matrix.transposeAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transposeAddEquiv [Add α] : Matrix m n α ≃+ Matrix n m α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.transpose_add`：transpose_add [Add α] (M : Matrix m n α) (N : Matr
ix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ

--- 原说明 ---
`Matrix.transpose` as an `AddEquiv`
-/
def transposeAddEquiv [Add α] : Matrix m n α ≃+ Matrix n m α where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  map_add' := transpose_add

@[simp]
/-
**Matrix.transposeAddEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transposeAddEquiv_symm [Add α] : (transposeAddEquiv m n α).symm = transpos
eAddEquiv n m α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transposeAddEquiv_symm [Add α] : (transposeAddEquiv m n α).symm = transposeAddEquiv n m α :=
  rfl

variable {m n α}
/-
**Matrix.transpose_list_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_list_sum [AddMonoid α] (l : List (Matrix m n α)) : l.sumᵀ = (l.m
ap transpose).sum
参数：l : List (Matrix m n α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem transpose_list_sum [AddMonoid α] (l : List (Matrix m n α)) :
    l.sumᵀ = (l.map transpose).sum :=
  map_list_sum (transposeAddEquiv m n α) l
/-
**Matrix.transpose_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix m n α)) : s
.sumᵀ = (s.map transpose).sum
参数：s : Multiset (Matrix m n α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_multiset_sum`：∀ {M : Type u_5} {N : Type u_6} [inst : A
ddCommMonoid M] [inst_1 : AddCommMonoid N] (f : M →+ N) (s : Multiset M),   f s.
sum = (Multiset.map…
-/
theorem transpose_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix m n α)) :
    s.sumᵀ = (s.map transpose).sum :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s
/-
**Matrix.transpose_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_sum [AddCommMonoid α] {ι : Type*} (s : Finset ι) (M : ι -> Matri
x m n α) : (∑ i in s, M i)ᵀ = ∑ i in s, (M i)ᵀ
参数：s : Finset ι；M : ι -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem transpose_sum [AddCommMonoid α] {ι : Type*} (s : Finset ι) (M : ι → Matrix m n α) :
    (∑ i ∈ s, M i)ᵀ = ∑ i ∈ s, (M i)ᵀ :=
  map_sum (transposeAddEquiv m n α) _ s

variable (m n R α)

/-- `Matrix.transpose` as a `LinearMap` -/
@[simps apply]
/-
**Matrix.transposeLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transposeLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] : Matrix 
m n α ≃ₗ[R] Matrix n m α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.transpose` as a `LinearMap`
-/
def transposeLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] :
    Matrix m n α ≃ₗ[R] Matrix n m α where
  __ := transposeAddEquiv m n α
  map_smul' := transpose_smul

@[simp]
/-
**Matrix.transposeLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transposeLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] : (t
ransposeLinearEquiv m n R α).symm = transposeLinearEquiv n m R α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transposeLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    (transposeLinearEquiv m n R α).symm = transposeLinearEquiv n m R α :=
  rfl

variable {m n R α}
variable (m α)

/-- `Matrix.transpose` as a `RingEquiv` to the opposite ring.

See also `RingEquiv.mopMatrix` for a version that doesn't require `α` to have commutative
multiplication, by taking its opposite. -/
@[simps!]
/-
**Matrix.transposeRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transposeRingEquiv [AddCommMonoid α] [CommMagma α] [Fintype m] : Matrix m 
m α ≃+* (Matrix m m α)ᵐᵒᵖ where .trans MulOpposite.opAddEquiv __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.transpose` as a `RingEquiv` to the opposite ring.

See also `RingEquiv.mopMatrix` for a version that doesn't require `α` to have co
mmutative
multiplication, by taking its opposite.
-/
def transposeRingEquiv [AddCommMonoid α] [CommMagma α] [Fintype m] :
    Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ where
  __ := transposeAddEquiv m m α |>.trans MulOpposite.opAddEquiv
  map_mul' M N := (congrArg MulOpposite.op <| transpose_mul M N).trans <| MulOpposite.op_mul ..

variable {m α}

@[simp]
/-
**Matrix.transpose_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_pow [CommSemiring α] [Fintype m] [DecidableEq m] (M : Matrix m m
 α) (k : Nat) : (M ^ k)ᵀ = Mᵀ ^ k
参数：M : Matrix m m α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem transpose_pow [CommSemiring α] [Fintype m] [DecidableEq m] (M : Matrix m m α) (k : ℕ) :
    (M ^ k)ᵀ = Mᵀ ^ k :=
  MulOpposite.op_injective <| map_pow (transposeRingEquiv m α) M k
/-
**Matrix.transpose_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_list_prod [CommSemiring α] [Fintype m] [DecidableEq m] (l : List
 (Matrix m m α)) : l.prodᵀ = (l.map transpose).reverse.prod
参数：l : List (Matrix m m α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.unop_map_list_prod`：∀ {R : Type u_2} {S : Type u_3} [inst : Se
miring R] [inst_1 : Semiring S] (f : R ≃+* Sᵐᵒᵖ) (l : List R),   MulOpposite.uno
p (f l.prod) = (Li…
-/
theorem transpose_list_prod [CommSemiring α] [Fintype m] [DecidableEq m] (l : List (Matrix m m α)) :
    l.prodᵀ = (l.map transpose).reverse.prod :=
  (transposeRingEquiv m α).unop_map_list_prod l

variable (R m α)

/-- `Matrix.transpose` as an `AlgEquiv` to the opposite ring.

See also `AlgEquiv.mopMatrix` for a version that doesn't require `α` to have commutative
multiplication, by taking its opposite. -/
@[simps!]
/-
**Matrix.transposeAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transposeAlgEquiv [CommSemiring R] [CommSemiring α] [Fintype m] [Decidable
Eq m] [Algebra R α] : Matrix m m α ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.transpose` as an `AlgEquiv` to the opposite ring.

See also `AlgEquiv.mopMatrix` for a version that doesn't require `α` to have com
mutative
multiplication, by taking its opposite.
-/
def transposeAlgEquiv [CommSemiring R] [CommSemiring α] [Fintype m] [DecidableEq m] [Algebra R α] :
    Matrix m m α ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ where
  __ := transposeRingEquiv m α
  commutes' r := by simp [algebraMap_eq_diagonal]

end Transpose

section NonUnitalNonAssocSemiring
variable {ι : Type*} [NonUnitalNonAssocSemiring α] [Fintype n]

/-
**Matrix.sum_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sum_mulVec (s : Finset ι) (x : ι -> Matrix m n α) (y : n -> α) : (∑ i in s
, x i) *ᵥ y = ∑ i in s, x i *ᵥ y
参数：s : Finset ι；x : ι -> Matrix m n α；y : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.sum_apply`：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finse
t β) (g : β -> Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
theorem sum_mulVec (s : Finset ι) (x : ι → Matrix m n α) (y : n → α) :
    (∑ i ∈ s, x i) *ᵥ y = ∑ i ∈ s, x i *ᵥ y := by
  ext
  simp only [mulVec, dotProduct, sum_apply, Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]
/-
**Matrix.mulVec_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_sum (x : Matrix m n α) (s : Finset ι) (y : ι -> (n -> α)) : x *ᵥ ∑ 
i in s, y i = ∑ i in s, x *ᵥ y i
参数：x : Matrix m n α；s : Finset ι；y : ι -> (n -> α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dotProduct_sum`：dotProduct_sum {ι : Type*} (u : m -> α) (s : Finset ι) (
v : ι -> (m -> α)) : u ⬝ᵥ ∑ i in s, v i = ∑ i in s, u ⬝ᵥ v i
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulVec_sum (x : Matrix m n α) (s : Finset ι) (y : ι → (n → α)) :
    x *ᵥ ∑ i ∈ s, y i = ∑ i ∈ s, x *ᵥ y i := by
  ext
  simp only [mulVec, dotProduct_sum, Finset.sum_apply]
/-
**Matrix.sum_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sum_vecMul (s : Finset ι) (x : ι -> (n -> α)) (y : Matrix n m α) : (∑ i in
 s, x i) ᵥ* y = ∑ i in s, x i ᵥ* y
参数：s : Finset ι；x : ι -> (n -> α)；y : Matrix n m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_dotProduct`：sum_dotProduct {ι : Type*} (s : Finset ι) (u : ι -> (m -
> α)) (v : m -> α) : (∑ i in s, u i) ⬝ᵥ v = ∑ i in s, u i ⬝ᵥ v
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_vecMul (s : Finset ι) (x : ι → (n → α)) (y : Matrix n m α) :
    (∑ i ∈ s, x i) ᵥ* y = ∑ i ∈ s, x i ᵥ* y := by
  ext
  simp only [vecMul, sum_dotProduct, Finset.sum_apply]
/-
**Matrix.vecMul_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_sum (x : n -> α) (s : Finset ι) (y : ι -> Matrix n m α) : x ᵥ* (∑ i
 in s, y i) = ∑ i in s, x ᵥ* y i
参数：x : n -> α；s : Finset ι；y : ι -> Matrix n m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.sum_apply`：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finse
t β) (g : β -> Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
theorem vecMul_sum (x : n → α) (s : Finset ι) (y : ι → Matrix n m α) :
    x ᵥ* (∑ i ∈ s, y i) = ∑ i ∈ s, x ᵥ* y i := by
  ext
  simp only [vecMul, dotProduct, sum_apply, Finset.mul_sum, Finset.sum_apply]
  rw [Finset.sum_comm]

end NonUnitalNonAssocSemiring

end Matrix

