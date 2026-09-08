/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

A key result is the orthogonality of characters for irreducible representations of finite group
over an algebraically closed field whose characteristic doesn't divide the order of the group. It
is the theorem `char_orthonormal`

## Implementation notes

Irreducible representations are implemented categorically, using the `CategoryTheory.Simple` class
defined in `Mathlib/CategoryTheory/Simple.lean`

## TODO
* Once we have the monoidal closed structure on `FDRep k G` and a better API for the rigid
  structure, `char_dual` and `char_linHom` should probably be stated
  in terms of `Vᘁ` and `ihom V W`.
-/

@[expose] public section


noncomputable section

universe u v

open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation Module

variable {k : Type u} [Field k]

namespace Representation

section Monoid

variable {G k V W : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

/-- The character of a representation `ρ : Representation k G V` is the function associating to
`g : G` the trace of the linear map `ρ g`. -/
/-
**Representation.character** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：character (g : G)
参数：g : G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The character of a representation `ρ : Representation k G V` is the function ass
ociating to
`g : G` the trace of the linear map `ρ g`.
-/
def character (g : G) :=
  LinearMap.trace k V (ρ g)

omit [FiniteDimensional k V] in
/-
**Representation.char_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：char_mul_comm (g : G) (h : G) : ρ.character (h * g) = ρ.character (g * h)
参数：g : G；h : G。
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
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem char_mul_comm (g : G) (h : G) :
    ρ.character (h * g) = ρ.character (g * h) := by simp only [trace_mul_comm, character, map_mul]

@[simp]
/-
**Representation.char_one** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：char_one (ρ : Representation k G V) : ρ.character 1 = Module.finrank k V
参数：ρ : Representation k G V。
该定理/引理给出了一组等式。
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
· 使用定理 `LinearMap.trace_one`：trace_one : trace R M 1 = (finrank R M : R)
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem char_one (ρ : Representation k G V) : ρ.character 1 = Module.finrank k V := by
  simp only [character, map_one, trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp]
/-
**Representation.char_tensor** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：char_tensor : (tprod ρ σ).character = ρ.character * σ.character
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.trace_tensorProduct'`：trace_tensorProduct' (f : M ->ₗ[R] M) (g
 : N ->ₗ[R] N) : trace R (M otimes N) (map f g) = trace R M f * trace R N g
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
The character is multiplicative under the tensor product.
-/
theorem char_tensor : (tprod ρ σ).character = ρ.character * σ.character := by
  ext g; convert! trace_tensorProduct' (ρ g) (σ g)

omit [FiniteDimensional k V] [FiniteDimensional k W] in
variable {ρ σ} in
/-- The character of isomorphic representations is the same. -/
/-
**Representation.char_iso** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：char_iso (φ : Equiv ρ σ) : ρ.character = σ.character
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Representation.Equiv.conj_apply_self`：∀ {A : Type u_1} {G : Type u_2} {V
 : Type u_3} {W : Type u_4} [inst : CommSemiring A] [inst_1 : Monoid G]   [inst_
2 : AddCommMonoid V] [inst…
· 使用定理 `LinearMap.trace_conj'`：trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : tr
ace R N (e.conj f) = trace R M f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The character of isomorphic representations is the same.
-/
theorem char_iso (φ : Equiv ρ σ) : ρ.character = σ.character := by
  ext g
  simp [character, ← φ.conj_apply_self]

end Monoid

section Group

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

omit [FiniteDimensional k V] in
/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
/-
**Representation.char_conj** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：char_conj (g : G) (h : G) : ρ.character (h * g * h⁻¹) = ρ.character g
参数：g : G；h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.char_mul_comm`：char_mul_comm (g : G) (h : G) : ρ.characte
r (h * g) = ρ.character (g * h)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b

--- 原说明 ---
The character of a representation is constant on conjugacy classes.
-/
theorem char_conj (g : G) (h : G) : ρ.character (h * g * h⁻¹) = ρ.character g := by
  rw [char_mul_comm, inv_mul_cancel_left]

@[simp]
/-
**Representation.char_dual** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：char_dual (g : G) : ρ.dual.character g = ρ.character g⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.trace_transpose'`：trace_transpose' (f : M ->ₗ[R] M) : trace R 
_ (Module.Dual.transpose (R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem char_dual (g : G) : ρ.dual.character g = ρ.character g⁻¹ :=
  trace_transpose' (ρ g⁻¹)

@[simp]
/-
**Representation.char_linHom** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：char_linHom (g : G) : (linHom ρ σ).character g = ρ.character g⁻¹ * σ.chara
cter g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Representation.char_iso`：char_iso (φ : Equiv ρ σ) : ρ.character = σ.char
acter
· 使用定理 `Representation.char_tensor`：char_tensor : (tprod ρ σ).character = ρ.char
acter * σ.character
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `Representation.char_dual`：char_dual (g : G) : ρ.dual.character g = ρ.cha
racter g⁻¹
-/
theorem char_linHom (g : G) :
    (linHom ρ σ).character g = ρ.character g⁻¹ * σ.character g := by
  rw [← char_iso (Equiv.dualTensorHom ρ σ), char_tensor, Pi.mul_apply, char_dual]

variable [Fintype G] [Invertible (Nat.card G : k)]
/-
**Representation.card_inv_mul_sum_char_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Rep
resentation`。
形式化陈述：card_inv_mul_sum_char_eq_finrank : (Nat.card G : k)⁻¹ * ∑ g : G, ρ.charact
er g = finrank k (invariants ρ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsProj.trace`：∀ {R : Type u_1} [inst : CommRing R] {M : Type u
_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodule R M}
 {f : M →ₗ[R…
· 使用定理 `Representation.isProj_averageMap`：isProj_averageMap : LinearMap.IsProj ρ
.invariants ρ.averageMap
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_inv_mul_sum_char_eq_finrank :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g = finrank k (invariants ρ) := by
  have : Invertible (Fintype.card G : k) := by rw [Fintype.card_eq_nat_card]; assumption
  rw [← (isProj_averageMap ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

/--
If `V` and `W` are finite-dimensional representations of a finite group, then the
scalar product of their characters is equal to the dimension of the space of
equivariant maps from `V` to `W`.
-/
/-
**Representation.card_inv_mul_sum_char_mul_char_eq_finrank** 是 Mathlib 中的一个定理，位于
命名空间 `Representation`。
形式化陈述：card_inv_mul_sum_char_mul_char_eq_finrank : (Nat.card G : k)⁻¹ * ∑ g : G, 
σ.character g * ρ.character g⁻¹ = finrank k (IntertwiningMap ρ σ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Representation.card_inv_mul_sum_char_eq_finrank`：card_inv_mul_sum_char_e
q_finrank : (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g = finrank k (invariants 
ρ)
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `V` and `W` are finite-dimensional representations of a finite group, then th
e
scalar product of their characters is equal to the dimension of the space of
equivariant maps from `V` to `W`.
-/
theorem card_inv_mul_sum_char_mul_char_eq_finrank :
    (Nat.card G : k)⁻¹ * ∑ g : G, σ.character g * ρ.character g⁻¹ =
      finrank k (IntertwiningMap ρ σ) := by
  simp_rw [mul_comm, ← char_linHom, card_inv_mul_sum_char_eq_finrank,
    (invariantsEquivIntertwiningMap ρ σ).finrank_eq]

end Group

section Orthogonality

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

variable [Fintype G] [Invertible (Nat.card G : k)] [IsAlgClosed k]

open scoped Classical in
/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
/-
**Representation.char_orthonormal** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：char_orthonormal [IsIrreducible ρ] [IsIrreducible σ] : (Nat.card G : k)⁻¹ 
* ∑ g : G, ρ.character g * σ.character g⁻¹ = if Nonempty (Equiv σ ρ) then ↑1 els
e ↑0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`：card_inv_mul_s
um_char_mul_char_eq_finrank : (Nat.card G : k)⁻¹ * ∑ g : G, σ.character g * ρ.ch
aracter g⁻¹ = finrank k (IntertwiningMap ρ σ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.finrank_eq_zero_of_subsingleton`：finrank_eq_zero_of_subsingleton 
[Module.Free R M] [Subsingleton M] : Module.finrank R M = 0
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Representation.IsIrreducible.instSubsingletonIntertwiningMapOfIsEmptyEqu
iv`：∀ {G : Type u_1} {k : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Monoid
 G] [inst_1 : Field k]   [inst_2 : AddCommGroup V] [inst_3 : _ro…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Representation.char_iso`：char_iso (φ : Equiv ρ σ) : ρ.character = σ.char
acter
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Representation.IsIrreducible.finrank_intertwiningMap_self`：∀ {G : Type u
_1} {k : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 : Field k] [inst_2 :
 AddCommGroup V]   [inst_3 : _root_.Module k V]…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
Orthogonality of characters for irreducible representations of finite group over
 an
algebraically closed field whose characteristic doesn't divide the order of the 
group.
-/
theorem char_orthonormal [IsIrreducible ρ] [IsIrreducible σ] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ =
      if Nonempty (Equiv σ ρ) then ↑1 else ↑0 := by
  cases isEmpty_or_nonempty (Equiv σ ρ)
  · rw [card_inv_mul_sum_char_mul_char_eq_finrank]
    simpa [finrank_eq_zero_of_subsingleton]
  · obtain φ : σ.Equiv ρ := Classical.choice inferInstance
    rw [char_iso φ, card_inv_mul_sum_char_mul_char_eq_finrank]
    simp

end Orthogonality

end Representation

namespace FDRep

section Monoid

variable {G : Type v} [Monoid G]

/-- The character of a representation `V : FDRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`. -/
/-
**FDRep.character** 是 Mathlib 中的一个定义，位于命名空间 `FDRep`。
形式化陈述：character (V : FDRep k G) (g : G)
参数：V : FDRep k G；g : G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The character of a representation `V : FDRep k G` is the function associating to
 `g : G` the
trace of the linear map `V.ρ g`.
-/
def character (V : FDRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)
/-
**FDRep.char_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：char_mul_comm (V : FDRep k G) (g : G) (h : G) : V.character (h * g) = V.ch
aracter (g * h)
参数：V : FDRep k G；g : G；h : G。
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
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem char_mul_comm (V : FDRep k G) (g : G) (h : G) :
    V.character (h * g) = V.character (g * h) := by simp only [trace_mul_comm, character, map_mul]

@[simp]
/-
**FDRep.char_one** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：char_one (V : FDRep k G) : V.character 1 = Module.finrank k V
参数：V : FDRep k G。
该定理/引理给出了一组等式。
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
· 使用定理 `LinearMap.trace_one`：trace_one : trace R M 1 = (finrank R M : R)
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FGModuleCat.instFiniteCarrier`：∀ (R : Type u) [inst : Ring R] (V : FGMod
uleCat R), Module.Finite R ↑V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem char_one (V : FDRep k G) : V.character 1 = Module.finrank k V := by
  simp only [character, map_one, trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp]
/-
**FDRep.char_tensor** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：char_tensor (V W : FDRep k G) : (V otimes W).character = V.character * W.c
haracter
参数：V W : FDRep k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.trace_tensorProduct'`：trace_tensorProduct' (f : M ->ₗ[R] M) (g
 : N ->ₗ[R] N) : trace R (M otimes N) (map f g) = trace R M f * trace R N g
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FGModuleCat.instFiniteCarrier`：∀ (R : Type u) [inst : Ring R] (V : FGMod
uleCat R), Module.Finite R ↑V

--- 原说明 ---
The character is multiplicative under the tensor product.
-/
theorem char_tensor (V W : FDRep k G) : (V ⊗ W).character = V.character * W.character := by
  ext g; convert! trace_tensorProduct' (V.ρ g) (W.ρ g)

/-- The character of isomorphic representations is the same. -/
/-
**FDRep.char_iso** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：char_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W.character
参数：i : V ≅ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FDRep.Iso.conj_ρ`：∀ {R : Type u} {G : Type v} [inst : CommRing R] [inst_
1 : Monoid G] {V W : FDRep R G} (i : V ≅ W) (g : G),   W.ρ g = (FDRep.isoToLinea
rEquiv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.trace_conj'`：trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : tr
ace R N (e.conj f) = trace R M f

--- 原说明 ---
The character of isomorphic representations is the same.
-/
theorem char_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W.character := by
  ext g
  simp only [character, FDRep.Iso.conj_ρ i]
  exact (trace_conj' (V.ρ g) _).symm

end Monoid

section Group

variable {G : Type v} [Group G]

/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
/-
**FDRep.char_conj** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：char_conj (V : FDRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.
character g
参数：V : FDRep k G；g : G；h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FDRep.char_mul_comm`：char_mul_comm (V : FDRep k G) (g : G) (h : G) : V.c
haracter (h * g) = V.character (g * h)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b

--- 原说明 ---
The character of a representation is constant on conjugacy classes.
-/
theorem char_conj (V : FDRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.character g := by
  rw [char_mul_comm, inv_mul_cancel_left]

@[simp]
/-
**FDRep.char_dual** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：char_dual (V : FDRep k G) (g : G) : (of (dual V.ρ)).character g = V.charac
ter g⁻¹
参数：V : FDRep k G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.trace_transpose'`：trace_transpose' (f : M ->ₗ[R] M) : trace R 
_ (Module.Dual.transpose (R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FGModuleCat.instFiniteCarrier`：∀ (R : Type u) [inst : Ring R] (V : FGMod
uleCat R), Module.Finite R ↑V
-/
theorem char_dual (V : FDRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)

@[simp]
/-
**FDRep.char_linHom** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：char_linHom (V W : FDRep k G) (g : G) : (of (linHom V.ρ W.ρ)).character g 
= V.character g⁻¹ * W.character g
参数：V W : FDRep k G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FGModuleCat.instFiniteCarrier`：∀ (R : Type u) [inst : Ring R] (V : FGMod
uleCat R), Module.Finite R ↑V
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FDRep.char_iso`：char_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W
.character
· 使用定理 `FDRep.char_tensor`：char_tensor (V W : FDRep k G) : (V otimes W).characte
r = V.character * W.character
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `FDRep.char_dual`：char_dual (V : FDRep k G) (g : G) : (of (dual V.ρ)).cha
racter g = V.character g⁻¹
-/
theorem char_linHom (V W : FDRep k G) (g : G) :
    (of (linHom V.ρ W.ρ)).character g = V.character g⁻¹ * W.character g := by
  rw [← char_iso (dualTensorIsoLinHom _ _), char_tensor, Pi.mul_apply, char_dual]

variable [Fintype G] [Invertible (Nat.card G : k)]
/-
**FDRep.average_char_eq_finrank_invariants** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：average_char_eq_finrank_invariants (V : FDRep k G) : (Nat.card G : k)⁻¹ * 
∑ g : G, V.character g = finrank k (invariants V.ρ)
参数：V : FDRep k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsProj.trace`：∀ {R : Type u_1} [inst : CommRing R] {M : Type u
_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodule R M}
 {f : M →ₗ[R…
· 使用定理 `Representation.isProj_averageMap`：isProj_averageMap : LinearMap.IsProj ρ
.invariants ρ.averageMap
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FGModuleCat.instFiniteCarrier`：∀ (R : Type u) [inst : Ring R] (V : FGMod
uleCat R), Module.Finite R ↑V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem average_char_eq_finrank_invariants (V : FDRep k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, V.character g = finrank k (invariants V.ρ) := by
  have : Invertible (Fintype.card G : k) := by
    rwa [Fintype.card_eq_nat_card]
  rw [← (isProj_averageMap V.ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

/--
If `V` and `W` are finite-dimensional representations of a finite group, then the
scalar product of their characters is equal to the dimension of the space of
equivariant maps from `V` to `W`.
-/
/-
**FDRep.scalar_product_char_eq_finrank_equivariant** 是 Mathlib 中的一个定理，位于命名空间 `FD
Rep`。
形式化陈述：scalar_product_char_eq_finrank_equivariant (V W : FDRep k G) : (Nat.card G
 : k)⁻¹ * ∑ g : G, W.character g * V.character g⁻¹ = Module.finrank k (V ⟶ W)
参数：V W : FDRep k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FGModuleCat.instFiniteCarrier`：∀ (R : Type u) [inst : Ring R] (V : FGMod
uleCat R), Module.Finite R ↑V
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FDRep.char_linHom`：char_linHom (V W : FDRep k G) (g : G) : (of (linHom V
.ρ W.ρ)).character g = V.character g⁻¹ * W.character g
· 使用定理 `FDRep.average_char_eq_finrank_invariants`：average_char_eq_finrank_invari
ants (V : FDRep k G) : (Nat.card G : k)⁻¹ * ∑ g : G, V.character g = finrank k (
invariants V.ρ)
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `FDRep.of_ρ'`：of_ρ' {V : Type u} [AddCommGroup V] [Module R V] [Module.Fi
nite R V] (ρ : G ->* V ->ₗ[R] V) : (of ρ).ρ = ρ

--- 原说明 ---
If `V` and `W` are finite-dimensional representations of a finite group, then th
e
scalar product of their characters is equal to the dimension of the space of
equivariant maps from `V` to `W`.
-/
theorem scalar_product_char_eq_finrank_equivariant (V W : FDRep k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, W.character g * V.character g⁻¹ =
    Module.finrank k (V ⟶ W) := by
  conv_lhs => congr; rfl; congr; rfl; intro _; rw [mul_comm, ← FDRep.char_linHom]
  -- The scalar product is the character of `Hom(V, W).`
  rw [FDRep.average_char_eq_finrank_invariants, ← LinearEquiv.finrank_eq
    (Representation.linHom.invariantsEquivFDRepHom V W), of_ρ']
  -- The average over the group of the character of a representation equals the dimension of the
  -- space of invariants, and the space of invariants of `Hom(V, W)` is the subspace of
  -- `G`-equivariant linear maps, `Hom_G(V, W)`.

end Group

section Orthogonality

variable {G : Type v} [Group G] [IsAlgClosed k]

variable [Fintype G] [Invertible (Nat.card G : k)]

open scoped Classical in
/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
/-
**FDRep.char_orthonormal** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：char_orthonormal (V W : FDRep k G) [Simple V] [Simple W] : (Nat.card G : k
)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ = if Nonempty (V ≅ W) then ↑1 els
e ↑0
参数：V W : FDRep k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FDRep.scalar_product_char_eq_finrank_equivariant`：scalar_product_char_eq
_finrank_equivariant (V W : FDRep k G) : (Nat.card G : k)⁻¹ * ∑ g : G, W.charact
er g * V.character g⁻¹ = Module.finran…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FDRep.finrank_hom_simple_simple`：finrank_hom_simple_simple [IsAlgClosed 
k] (V W : FDRep k G) [Simple V] [Simple W] : finrank k (V ⟶ W) = if Nonempty (V 
≅ W) then 1 else 0
· 使用定理 `CategoryTheory.Iso.nonempty_iso_symm`：nonempty_iso_symm (X Y : C) : None
mpty (X ≅ Y) ↔ Nonempty (Y ≅ X)

--- 原说明 ---
Orthogonality of characters for irreducible representations of finite group over
 an
algebraically closed field whose characteristic doesn't divide the order of the 
group.
-/
theorem char_orthonormal (V W : FDRep k G) [Simple V] [Simple W] :
    (Nat.card G : k)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 := by
  rw [scalar_product_char_eq_finrank_equivariant]
  -- The scalar product of the characters is equal to the dimension of the space of
  -- equivariant maps `W ⟶ V`.
  rw_mod_cast [finrank_hom_simple_simple W V, Iso.nonempty_iso_symm]
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` if `V ≅ W` and `0` otherwise.

end Orthogonality

end FDRep

