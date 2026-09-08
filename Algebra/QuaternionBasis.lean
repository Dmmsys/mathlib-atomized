/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Quaternion
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Basis on a quaternion-like algebra

## Main definitions

* `QuaternionAlgebra.Basis A c₁ c₂ c₃`: a basis for a subspace of an `R`-algebra `A` that has the
  same algebra structure as `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.Basis.self R`: the canonical basis for `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.Basis.compHom b f`: transform a basis `b` by an AlgHom `f`.
* `QuaternionAlgebra.lift`: Define an `AlgHom` out of `ℍ[R,c₁,c₂,c₃]` by its action on the basis
  elements `i`, `j`, and `k`. In essence, this is a universal property. Analogous to `Complex.lift`,
  but takes a bundled `QuaternionAlgebra.Basis` instead of just a `Subtype` as the amount of
  data / proofs is non-negligible.
-/

@[expose] public section


open Quaternion

namespace QuaternionAlgebra

/-- A quaternion basis contains the information both sufficient and necessary to construct an
`R`-algebra homomorphism from `ℍ[R,c₁,c₂,c₃]` to `A`; or equivalently, a surjective
`R`-algebra homomorphism from `ℍ[R,c₁,c₂,c₃]` to an `R`-subalgebra of `A`.

Note that for definitional convenience, `k` is provided as a field even though `i_mul_j` fully
determines it. -/
/-
**QuaternionAlgebra.Basis** 是 Mathlib 中的一个归纳类型，位于命名空间 `QuaternionAlgebra`。
形式化陈述：{R : Type u_1} → (A : Type u_2) → [inst : CommRing R] → [inst_1 : Ring A] 
→ [Algebra R A] → R → R → R → Type u_2
参数：A : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quaternion basis contains the information both sufficient and necessary to con
struct an
`R`-algebra homomorphism from `ℍ[R,c₁,c₂,c₃]` to `A`; or equivalently, a surject
ive
`R`-algebra homomorphism from `ℍ[R,c₁,c₂,c₃]` to an `R`-subalgebra of `A`.

Note that for definitional convenience, `k` is provided as a field even though `
i_mul_j` fully
determines it.
-/
structure Basis {R : Type*} (A : Type*) [CommRing R] [Ring A] [Algebra R A] (c₁ c₂ c₃ : R) where
  /-- The first imaginary unit -/
  i : A
  /-- The second imaginary unit -/
  j : A
  /-- The third imaginary unit -/
  k : A
  i_mul_i : i * i = c₁ • (1 : A) + c₂ • i
  j_mul_j : j * j = c₃ • (1 : A)
  i_mul_j : i * j = k
  j_mul_i : j * i = c₂ • j - k

initialize_simps_projections Basis
  (as_prefix i, as_prefix j, as_prefix k)

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable {c₁ c₂ c₃ : R}

namespace Basis

/-- Since `k` is redundant, it is not necessary to show `q₁.k = q₂.k` when showing `q₁ = q₂`. -/
@[ext]
/-
**QuaternionAlgebra.Basis.ext** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.Basis
`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {c₁ c₂ c₃ : R}   ⦃q₁ q₂ : QuaternionAlgebra.Basis A c₁ c₂ c₃⦄
, q₁.i = q₂.i → q₁.j = q₂.j → q₁ = q₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Since `k` is redundant, it is not necessary to show `q₁.k = q₂.k` when showing `
q₁ = q₂`.
-/
protected theorem ext ⦃q₁ q₂ : Basis A c₁ c₂ c₃⦄ (hi : q₁.i = q₂.i)
    (hj : q₁.j = q₂.j) : q₁ = q₂ := by
  cases q₁; cases q₂; grind

variable (R) in
/-- There is a natural quaternionic basis for the `QuaternionAlgebra`. -/
@[simps i j k]
/-
**QuaternionAlgebra.Basis.self** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra.Basi
s`。
形式化陈述：(R : Type u_1) → [inst : CommRing R] → {c₁ c₂ c₃ : R} → QuaternionAlgebra.
Basis (QuaternionAlgebra R c₁ c₂ c₃) c₁ c₂ c₃
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a natural quaternionic basis for the `QuaternionAlgebra`.
-/
protected def self : Basis ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃ where
  i := ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp
  j := ⟨0, 0, 1, 0⟩
  j_mul_j := by ext <;> simp
  k := ⟨0, 0, 0, 1⟩
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp
/-
**QuaternionAlgebra.Basis.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Basis ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃) :=
  ⟨Basis.self R⟩

variable (q : Basis A c₁ c₂ c₃)

attribute [simp] i_mul_i j_mul_j i_mul_j j_mul_i

@[simp]
/-
**QuaternionAlgebra.Basis.i_mul_k** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.B
asis`。
形式化陈述：i_mul_k : q.i * q.k = c₁ • q.j + c₂ • q.k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuaternionAlgebra.Basis.i_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `QuaternionAlgebra.Basis.i_mul_i`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem i_mul_k : q.i * q.k = c₁ • q.j + c₂ • q.k := by
  rw [← i_mul_j, ← mul_assoc, i_mul_i, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]

@[simp]
/-
**QuaternionAlgebra.Basis.k_mul_i** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.B
asis`。
形式化陈述：k_mul_i : q.k * q.i = -c₁ • q.j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuaternionAlgebra.Basis.i_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `QuaternionAlgebra.Basis.j_mul_i`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `QuaternionAlgebra.Basis.i_mul_k`：i_mul_k : q.i * q.k = c₁ • q.j + c₂ • q
.k
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.zero_eq_eval`：zero_eq_eval [AddMonoid M] : (0:M
) = NF.eval (R
· 使用定理 `Mathlib.Tactic.Module.NF.neg_eq_eval`：neg_eq_eval [AddCommGroup M] [Semi
ring S] [Module S M] [Ring R] [Module R M] {l : NF R M} {l₀ : NF S M} (hl : l.ev
al = l₀.eval) {x : M} (h :…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_const`：eq_cons_const [AddCommMonoid M] 
[Semiring R] [Module R M] {r : R} (m : M) {n : M} {l : NF R M} (h1 : r = 0) (h2 
: l.eval = n) : ((r, m) ::ᵣ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 63 条，此处仅展示前 30 条）
-/
theorem k_mul_i : q.k * q.i = -c₁ • q.j := by
  rw [← i_mul_j, mul_assoc, j_mul_i, mul_sub, i_mul_k, neg_smul, mul_smul_comm, i_mul_j]
  linear_combination (norm := module)

@[simp]
/-
**QuaternionAlgebra.Basis.k_mul_j** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.B
asis`。
形式化陈述：k_mul_j : q.k * q.j = c₃ • q.i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuaternionAlgebra.Basis.i_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `QuaternionAlgebra.Basis.j_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem k_mul_j : q.k * q.j = c₃ • q.i := by
  rw [← i_mul_j, mul_assoc, j_mul_j, mul_smul_comm, mul_one]

@[simp]
/-
**QuaternionAlgebra.Basis.j_mul_k** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.B
asis`。
形式化陈述：j_mul_k : q.j * q.k = (c₂ * c₃) • 1 - c₃ • q.i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuaternionAlgebra.Basis.i_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `QuaternionAlgebra.Basis.j_mul_i`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `QuaternionAlgebra.Basis.j_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `QuaternionAlgebra.Basis.k_mul_j`：k_mul_j : q.k * q.j = c₃ • q.i
-/
theorem j_mul_k : q.j * q.k = (c₂ * c₃) • 1 - c₃ • q.i := by
  rw [← i_mul_j, ← mul_assoc, j_mul_i, sub_mul, smul_mul_assoc, j_mul_j, ← smul_assoc, k_mul_j]
  rfl

@[simp]
/-
**QuaternionAlgebra.Basis.k_mul_k** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.B
asis`。
形式化陈述：k_mul_k : q.k * q.k = -((c₁ * c₃) • (1 : A))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuaternionAlgebra.Basis.i_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `QuaternionAlgebra.Basis.j_mul_i`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `QuaternionAlgebra.Basis.i_mul_i`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuaternionAlgebra.Basis.j_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
（共 71 条，此处仅展示前 30 条）
-/
theorem k_mul_k : q.k * q.k = -((c₁ * c₃) • (1 : A)) := by
  rw [← i_mul_j, mul_assoc, ← mul_assoc q.j _ _, j_mul_i, ← i_mul_j, ← mul_assoc, mul_sub, ←
    mul_assoc, i_mul_i, add_mul, smul_mul_assoc, one_mul, sub_mul, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, mul_assoc, j_mul_j, add_mul, smul_mul_assoc, j_mul_j, smul_smul,
    smul_mul_assoc, mul_assoc, j_mul_j]
  linear_combination (norm := module)


/-- Intermediate result used to define `QuaternionAlgebra.Basis.liftHom`. -/
/-
**QuaternionAlgebra.Basis.lift** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra.Basi
s`。
形式化陈述：lift (x : ℍ[R,c₁,c₂,c₃]) : A
参数：x : ℍ[R,c₁,c₂,c₃]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate result used to define `QuaternionAlgebra.Basis.liftHom`.
-/
def lift (x : ℍ[R,c₁,c₂,c₃]) : A :=
  algebraMap R _ x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k
/-
**QuaternionAlgebra.Basis.lift_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra
.Basis`。
形式化陈述：lift_zero : q.lift (0 : ℍ[R,c₁,c₂,c₃]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_zero : q.lift (0 : ℍ[R,c₁,c₂,c₃]) = 0 := by simp [lift]
/-
**QuaternionAlgebra.Basis.lift_one** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.
Basis`。
形式化陈述：lift_one : q.lift (1 : ℍ[R,c₁,c₂,c₃]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_one : q.lift (1 : ℍ[R,c₁,c₂,c₃]) = 1 := by simp [lift]
/-
**QuaternionAlgebra.Basis.lift_add** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.
Basis`。
形式化陈述：lift_add (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x + y) = q.lift x + q.lift y
参数：x y : ℍ[R,c₁,c₂,c₃]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `_private.Mathlib.Algebra.QuaternionBasis.0.QuaternionAlgebra.Basis.lift_
add._abel_1_2`：∀ {R : Type u_2} {A : Type u_1} [inst : CommRing R] [inst_1 : Rin
g A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (q : QuaternionAlgebra.Basis A…
-/
theorem lift_add (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x + y) = q.lift x + q.lift y := by
  simp only [lift, re_add, map_add, imI_add, add_smul, imJ_add, imK_add]
  abel
/-
**QuaternionAlgebra.Basis.lift_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.
Basis`。
形式化陈述：lift_mul (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x * y) = q.lift x * q.lift y
参数：x y : ℍ[R,c₁,c₂,c₃]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `QuaternionAlgebra.Basis.i_mul_i`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `QuaternionAlgebra.Basis.i_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `QuaternionAlgebra.Basis.i_mul_k`：i_mul_k : q.i * q.k = c₁ • q.j + c₂ • q
.k
· 使用定理 `QuaternionAlgebra.Basis.j_mul_i`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `QuaternionAlgebra.Basis.j_mul_j`：∀ {R : Type u_1} {A : Type u_2} [inst :
 CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (self : Q
uaternionAlgebra.Basi…
· 使用定理 `QuaternionAlgebra.Basis.j_mul_k`：j_mul_k : q.j * q.k = (c₂ * c₃) • 1 - c
₃ • q.i
· 使用定理 `QuaternionAlgebra.Basis.k_mul_i`：k_mul_i : q.k * q.i = -c₁ • q.j
· 使用定理 `QuaternionAlgebra.Basis.k_mul_j`：k_mul_j : q.k * q.j = c₃ • q.i
· 使用定理 `QuaternionAlgebra.Basis.k_mul_k`：k_mul_k : q.k * q.k = -((c₁ * c₃) • (1 
: A))
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 91 条，此处仅展示前 30 条）
-/
theorem lift_mul (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x * y) = q.lift x * q.lift y := by
  simp only [lift, Algebra.algebraMap_eq_smul_one]
  simp_rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, i_mul_k, k_mul_i, k_mul_j, j_mul_k, k_mul_k]
  simp only [smul_smul, smul_neg, sub_eq_add_neg, ← add_assoc, neg_smul]
  simp only [mul_right_comm _ _ (c₁ * c₃), mul_comm _ (c₁ * c₃)]
  simp only [mul_comm _ c₁]
  simp only [mul_right_comm _ _ c₃]
  simp only [← mul_assoc]
  simp only [re_mul, sub_eq_add_neg, add_smul, neg_smul, imI_mul, ← add_assoc, imJ_mul, imK_mul]
  linear_combination (norm := module)
/-
**QuaternionAlgebra.Basis.lift_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra
.Basis`。
形式化陈述：lift_smul (r : R) (x : ℍ[R,c₁,c₂,c₃]) : q.lift (r • x) = r • q.lift x
参数：r : R；x : ℍ[R,c₁,c₂,c₃]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_smul (r : R) (x : ℍ[R,c₁,c₂,c₃]) : q.lift (r • x) = r • q.lift x := by
  simp [lift, mul_smul, ← Algebra.smul_def]

/-- A `QuaternionAlgebra.Basis` implies an `AlgHom` from the quaternions. -/
@[simps!]
/-
**QuaternionAlgebra.Basis.liftHom** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra.B
asis`。
形式化陈述：liftHom : ℍ[R,c₁,c₂,c₃] ->ₐ[R] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.Basis.lift_one`：lift_one : q.lift (1 : ℍ[R,c₁,c₂,c₃]) 
= 1
· 使用定理 `QuaternionAlgebra.Basis.lift_mul`：lift_mul (x y : ℍ[R,c₁,c₂,c₃]) : q.lif
t (x * y) = q.lift x * q.lift y
· 使用定理 `QuaternionAlgebra.Basis.lift_zero`：lift_zero : q.lift (0 : ℍ[R,c₁,c₂,c₃]
) = 0
· 使用定理 `QuaternionAlgebra.Basis.lift_add`：lift_add (x y : ℍ[R,c₁,c₂,c₃]) : q.lif
t (x + y) = q.lift x + q.lift y
· 使用定理 `QuaternionAlgebra.Basis.lift_smul`：lift_smul (r : R) (x : ℍ[R,c₁,c₂,c₃])
 : q.lift (r • x) = r • q.lift x

--- 原说明 ---
A `QuaternionAlgebra.Basis` implies an `AlgHom` from the quaternions.
-/
def liftHom : ℍ[R,c₁,c₂,c₃] →ₐ[R] A :=
  AlgHom.mk'
    { toFun := q.lift
      map_zero' := q.lift_zero
      map_one' := q.lift_one
      map_add' := q.lift_add
      map_mul' := q.lift_mul } q.lift_smul

@[simp]
/-
**QuaternionAlgebra.Basis.range_liftHom** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlg
ebra.Basis`。
形式化陈述：range_liftHom (B : Basis A c₁ c₂ c₃) : (liftHom B).range = Algebra.adjoin 
R {B.i, B.j, B.k}
参数：B : Basis A c₁ c₂ c₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `QuaternionAlgebra.Basis.i_self`：∀ (R : Type u_1) [inst : CommRing R] {c₁
 c₂ c₃ : R},   (QuaternionAlgebra.Basis.self R).i = { re := 0, imI := 1, imJ := 
0, imK := 0 }
· 使用定理 `QuaternionAlgebra.Basis.liftHom_apply`：∀ {R : Type u_1} {A : Type u_2} [
inst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   (q 
: QuaternionAlgebra.Basis A…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 32 条，此处仅展示前 30 条）
-/
theorem range_liftHom (B : Basis A c₁ c₂ c₃) :
    (liftHom B).range = Algebra.adjoin R {B.i, B.j, B.k} := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact algebraMap_mem _ _
    all_goals
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin <| by simp) _
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | rfl | rfl)
      <;> [use (Basis.self R).i; use (Basis.self R).j; use (Basis.self R).k]
    all_goals simp [lift]

/-- Transform a `QuaternionAlgebra.Basis` through an `AlgHom`. -/
@[simps i j k]
/-
**QuaternionAlgebra.Basis.compHom** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra.B
asis`。
形式化陈述：compHom (F : A ->ₐ[R] B) : Basis B c₁ c₂ c₃ where i
参数：F : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transform a `QuaternionAlgebra.Basis` through an `AlgHom`.
-/
def compHom (F : A →ₐ[R] B) : Basis B c₁ c₂ c₃ where
  i := F q.i
  i_mul_i := by rw [← map_mul, q.i_mul_i, map_add, map_smul, map_smul, map_one]
  j := F q.j
  j_mul_j := by rw [← map_mul, q.j_mul_j, map_smul, map_one]
  k := F q.k
  i_mul_j := by rw [← map_mul, q.i_mul_j]
  j_mul_i := by rw [← map_mul, q.j_mul_i, map_sub, map_smul]

end Basis

set_option backward.defeqAttrib.useBackward true in
/-- A quaternionic basis on `A` is equivalent to a map from the quaternion algebra to `A`. -/
@[simps]
/-
**QuaternionAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：lift : Basis A c₁ c₂ c₃ ≃ (ℍ[R,c₁,c₂,c₃] ->ₐ[R] A) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quaternionic basis on `A` is equivalent to a map from the quaternion algebra t
o `A`.
-/
def lift : Basis A c₁ c₂ c₃ ≃ (ℍ[R,c₁,c₂,c₃] →ₐ[R] A) where
  toFun := Basis.liftHom
  invFun := (Basis.self R).compHom
  left_inv q := by ext <;> simp [Basis.lift]
  right_inv F := by
    ext
    dsimp [Basis.lift]
    rw [← F.commutes]
    simp only [← map_smul, ← map_add, mk_add_mk, smul_mk, smul_zero, algebraMap_eq]
    congr <;> simp

/-- Two `R`-algebra morphisms from a quaternion algebra are equal if they agree on `i` and `j`. -/
@[ext]
/-
**QuaternionAlgebra.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：hom_ext ⦃f g : ℍ[R,c₁,c₂,c₃] ->ₐ[R] A⦄ (hi : f (Basis.self R).i = g (Basis
.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `QuaternionAlgebra.Basis.ext`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {c₁ c₂ c₃ : R}   ⦃q₁ q₂ : Quat
ernionAlgebra.Bas…

--- 原说明 ---
Two `R`-algebra morphisms from a quaternion algebra are equal if they agree on `
i` and `j`.
-/
theorem hom_ext ⦃f g : ℍ[R,c₁,c₂,c₃] →ₐ[R] A⦄
    (hi : f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) :
    f = g :=
  lift.symm.injective <| Basis.ext hi hj

end QuaternionAlgebra

namespace Quaternion
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

open QuaternionAlgebra (Basis)

/-- Two `R`-algebra morphisms from the quaternions are equal if they agree on `i` and `j`. -/
@[ext]
/-
**Quaternion.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：hom_ext ⦃f g : ℍ[R] ->ₐ[R] A⦄ (hi : f (Basis.self R).i = g (Basis.self R).
i) (hj : f (Basis.self R).j = g (Basis.self R).j) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.hom_ext`：hom_ext ⦃f g : ℍ[R,c₁,c₂,c₃] ->ₐ[R] A⦄ (hi : 
f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.sel
f R).j) : f = g

--- 原说明 ---
Two `R`-algebra morphisms from the quaternions are equal if they agree on `i` an
d `j`.
-/
theorem hom_ext ⦃f g : ℍ[R] →ₐ[R] A⦄
    (hi : f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) :
    f = g :=
  QuaternionAlgebra.hom_ext hi hj

end Quaternion

