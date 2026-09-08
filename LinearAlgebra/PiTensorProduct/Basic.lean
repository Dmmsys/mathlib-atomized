/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Multilinear.TensorProduct
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Tensor product of an indexed family of modules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of modules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `FreeAddMonoid (R × Π i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`.

## Main definitions

* `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `liftAddHom` constructs an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × Π i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : MultilinearMap R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`. This is bundled as a linear equivalence.
* `PiTensorProduct.reindex e` re-indexes the components of `⨂[R] i : ι, M` along `e : ι ≃ ι₂`.
* `PiTensorProduct.tmulEquiv` equivalence between a `TensorProduct` of `PiTensorProduct`s and
  a single `PiTensorProduct`.

## Notation

* `⨂[R] i, s i` is defined as localized notation in scope `TensorProduct`.
* `⨂ₜ[R] i, f i` with `f : ∀ i, s i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

* We define it via `FreeAddMonoid (R × Π i, s i)` with the `R` representing a "hidden" tensor
  factor, rather than `FreeAddMonoid (Π i, s i)` to ensure that, if `ι` is an empty type,
  the space is isomorphic to the base ring `R`.
* We have not restricted the index type `ι` to be a `Fintype`, as nothing we do here strictly
  requires it. However, problems may arise in the case where `ι` is infinite; use at your own
  caution.
* Instead of requiring `DecidableEq ι` as an argument to `PiTensorProduct` itself, we include it
  as an argument in the constructors of the relation. A decidability instance still has to come
  from somewhere due to the use of `Function.update`, but this hides it from the downstream user.
  See the implementation notes for `MultilinearMap` for an extended discussion of this choice.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/

@[expose] public section

open Function

section Semiring

variable {ι ι₂ ι₃ : Type*}
variable {R : Type*} [CommSemiring R]
variable {R₁ R₂ : Type*}
variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {E : Type*} [AddCommMonoid E] [Module R E]
variable {F : Type*} [AddCommMonoid F]

namespace PiTensorProduct

variable (R) (s)

/-- The relation on `FreeAddMonoid (R × Π i, s i)` that generates a congruence whose quotient is
the tensor product. -/
/-
**PiTensorProduct.Eqv** 是 Mathlib 中的一个归纳类型，位于命名空间 `PiTensorProduct`。
形式化陈述：{ι : Type u_1} →   (R : Type u_4) →     [inst : CommSemiring R] →       (s
 : ι → Type u_7) →         [inst_1 : (i : ι) → AddCommMonoid (s i)] →           
[(i : ι) → _root_.Module R (s i)] →             FreeAddMonoid (R × ((i : ι) → s 
i)) → FreeAddMonoid (R × ((i : ι) → s i)) → Prop
参数：R : Type u_4；s : ι → Type u_7；i : ι；s i；i : ι；s i；R × ((i : ι) → s i)；R × ((i
 : ι) → s i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation on `FreeAddMonoid (R × Π i, s i)` that generates a congruence whose
 quotient is
the tensor product.
-/
inductive Eqv : FreeAddMonoid (R × Π i, s i) → FreeAddMonoid (R × Π i, s i) → Prop
  | of_zero : ∀ (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), Eqv (FreeAddMonoid.of (r, f)) 0
  | of_zero_scalar : ∀ f : Π i, s i, Eqv (FreeAddMonoid.of (0, f)) 0
  | of_add : ∀ (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
      Eqv (FreeAddMonoid.of (r, update f i m₁) + FreeAddMonoid.of (r, update f i m₂))
        (FreeAddMonoid.of (r, update f i (m₁ + m₂)))
  | of_add_scalar : ∀ (r r' : R) (f : Π i, s i),
      Eqv (FreeAddMonoid.of (r, f) + FreeAddMonoid.of (r', f)) (FreeAddMonoid.of (r + r', f))
  | of_smul : ∀ (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (r' : R),
      Eqv (FreeAddMonoid.of (r, update f i (r' • f i))) (FreeAddMonoid.of (r' * r, f))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)

end PiTensorProduct

variable (R) (s)

/-- `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor
  product of all the `s i`'s. This is denoted by `⨂[R] i, s i`. -/
/-
**PiTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PiTensorProduct : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the
 tensor
  product of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
-/
def PiTensorProduct : Type _ :=
  (addConGen (PiTensorProduct.Eqv R s)).Quotient

variable {R}

/-- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product `PiTensorProduct`,
given an indexed family of types `s : ι → Type*`. -/
scoped[TensorProduct] notation3:100"⨂["R"] "(...)", "r:(scoped f => PiTensorProduct R f) => r

open TensorProduct

namespace PiTensorProduct

section Module

/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (⨂[R] i, s i) :=
  { (addConGen (PiTensorProduct.Eqv R s)).addMonoid with
    add_comm := fun x y ↦
      AddCon.induction_on₂ x y fun _ _ ↦
        Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.add_comm _ _ }
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (⨂[R] i, s i) := ⟨0⟩

variable (R) {s}

/-- `tprodCoeff R r f` with `r : R` and `f : Π i, s i` is the tensor product of the vectors `f i`
over all `i : ι`, multiplied by the coefficient `r`. Note that this is meant as an auxiliary
definition for this file alone, and that one should use `tprod` defined below for most purposes. -/
/-
**PiTensorProduct.tprodCoeff** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：tprodCoeff (r : R) (f : Π i, s i) : ⨂[R] i, s i
参数：r : R；f : Π i, s i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`tprodCoeff R r f` with `r : R` and `f : Π i, s i` is the tensor product of the 
vectors `f i`
over all `i : ι`, multiplied by the coefficient `r`. Note that this is meant as 
an auxiliary
definition for this file alone, and that one should use `tprod` defined below fo
r most purposes.
-/
def tprodCoeff (r : R) (f : Π i, s i) : ⨂[R] i, s i :=
  AddCon.mk' _ <| FreeAddMonoid.of (r, f)

variable {R}
/-
**PiTensorProduct.zero_tprodCoeff** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：zero_tprodCoeff (f : Π i, s i) : tprodCoeff R 0 f = 0
参数：f : Π i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem zero_tprodCoeff (f : Π i, s i) : tprodCoeff R 0 f = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_scalar _
/-
**PiTensorProduct.zero_tprodCoeff'** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：zero_tprodCoeff' (z : R) (f : Π i, s i) (i : ι) (hf : f i = 0) : tprodCoef
f R z f = 0
参数：z : R；f : Π i, s i；i : ι；hf : f i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem zero_tprodCoeff' (z : R) (f : Π i, s i) (i : ι) (hf : f i = 0) : tprodCoeff R z f = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero _ _ i hf
/-
**PiTensorProduct.add_tprodCoeff** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：add_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i
) : tprodCoeff R z (update f i m₁) + tprodCoeff R z (update f i m₂) = tprodCoeff
 R z (update f i (m₁ + m₂))
参数：z : R；f : Π i, s i；i : ι；m₁ m₂ : s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem add_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
    tprodCoeff R z (update f i m₁) + tprodCoeff R z (update f i m₂) =
      tprodCoeff R z (update f i (m₁ + m₂)) :=
  Quotient.sound' <| AddConGen.Rel.of _ _ (Eqv.of_add _ z f i m₁ m₂)
/-
**PiTensorProduct.add_tprodCoeff'** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：add_tprodCoeff' (z₁ z₂ : R) (f : Π i, s i) : tprodCoeff R z₁ f + tprodCoef
f R z₂ f = tprodCoeff R (z₁ + z₂) f
参数：z₁ z₂ : R；f : Π i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem add_tprodCoeff' (z₁ z₂ : R) (f : Π i, s i) :
    tprodCoeff R z₁ f + tprodCoeff R z₂ f = tprodCoeff R (z₁ + z₂) f :=
  Quotient.sound' <| AddConGen.Rel.of _ _ (Eqv.of_add_scalar z₁ z₂ f)
/-
**PiTensorProduct.smul_tprodCoeff_aux** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct
`。
形式化陈述：smul_tprodCoeff_aux [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R)
 : tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r * z) f
参数：z : R；f : Π i, s i；i : ι；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem smul_tprodCoeff_aux [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R) :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r * z) f :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _ _ _
/-
**PiTensorProduct.smul_tprodCoeff** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：smul_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R₁) [S
Mul R₁ R] [IsScalarTower R₁ R R] [SMul R₁ (s i)] [IsScalarTower R₁ R (s i)] : tp
rodCoeff R z (update f i (r • f i)) = tprodCoeff R (r • z) f
参数：z : R；f : Π i, s i；i : ι；r : R₁；s i；s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `PiTensorProduct.smul_tprodCoeff_aux`：smul_tprodCoeff_aux [DecidableEq ι]
 (z : R) (f : Π i, s i) (i : ι) (r : R) : tprodCoeff R z (update f i (r • f i)) 
= tprodCoeff R (r * z) f
-/
theorem smul_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R₁) [SMul R₁ R]
    [IsScalarTower R₁ R R] [SMul R₁ (s i)] [IsScalarTower R₁ R (s i)] :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r • z) f := by
  have h₁ : r • z = r • (1 : R) * z := by rw [smul_mul_assoc, one_mul]
  have h₂ : r • f i = (r • (1 : R)) • f i := (smul_one_smul _ _ _).symm
  rw [h₁, h₂]
  exact smul_tprodCoeff_aux z f i _

/-- Construct an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a function
`φ : (R × Π i, s i) → F` with the appropriate properties. -/
/-
**PiTensorProduct.liftAddHom** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：liftAddHom (φ : (R × Π i, s i) -> F) (C0 : forall (r : R) (f : Π i, s i) (
i : ι) (_ : f i = 0), φ (r, f) = 0) (C0' : forall f : Π i, s i, φ (0, f) = 0) (C
_add : forall [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i), φ (r
, update f i m₁) + φ (r, update f i m₂) = φ (r, update f i (m₁ + m₂))) (C_add_sc
alar : forall (r r' : R) (f : Π i, s i), φ (r, f) + φ (r', f) = φ (r + r', f)) (
C_smul : forall [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (r' : R), φ (r, u
pdate f i (r' • f i)) = φ 
参数：φ : (R × Π i, s i) -> F；C0 : forall (r : R) (f : Π i, s i) (i : ι) (_ : f i =
 0), φ (r, f) = 0；C0' : forall f : Π i, s i, φ (0, f) = 0；C_add : forall [Decida
bleEq ι] (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i), φ (r, update f i m₁) + φ 
(r, update f i m₂) = φ (r, update f i (m₁ + m₂))；C_add_scalar : forall (r r' : R
) (f : Π i, s i), φ (r, f) + φ (r', f) = φ (r + r', f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a functi
on
`φ : (R × Π i, s i) → F` with the appropriate properties.
-/
def liftAddHom (φ : (R × Π i, s i) → F)
    (C0 : ∀ (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), φ (r, f) = 0)
    (C0' : ∀ f : Π i, s i, φ (0, f) = 0)
    (C_add : ∀ [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
      φ (r, update f i m₁) + φ (r, update f i m₂) = φ (r, update f i (m₁ + m₂)))
    (C_add_scalar : ∀ (r r' : R) (f : Π i, s i), φ (r, f) + φ (r', f) = φ (r + r', f))
    (C_smul : ∀ [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (r' : R),
      φ (r, update f i (r' • f i)) = φ (r' * r, f)) :
    (⨂[R] i, s i) →+ F :=
  (addConGen (PiTensorProduct.Eqv R s)).lift (FreeAddMonoid.lift φ) <|
    AddCon.addConGen_le.2 fun x y hxy ↦
      match hxy with
      | Eqv.of_zero r' f i hf =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C0 r' f i hf]
      | Eqv.of_zero_scalar f =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C0']
      | Eqv.of_add inst z f i m₁ m₂ =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, @C_add inst]
      | Eqv.of_add_scalar z₁ z₂ f =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C_add_scalar]
      | Eqv.of_smul inst z f i r' =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, @C_smul inst]
      | Eqv.add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]

/-- Induct using `tprodCoeff` -/
@[elab_as_elim]
/-
**PiTensorProduct.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {motive : (PiTensorProduct R fun i => s i) → Prop}   (z : PiTensorProduct
 R fun i => s i),   (∀ (r : R) (f : (i : ι) → s i), motive (PiTensorProduct.tpro
dCoeff R r f)) →     (∀ (x y : PiTensorProduct R fun i => s i), motive x → motiv
e y → motive (x + y)) → motive z
参数：i : ι；s i；i : ι；s i；PiTensorProduct R fun i => s i；z : PiTensorProduct R fun 
i => s i；∀ (r : R) (f : (i : ι) → s i), motive (PiTensorProduct.tprodCoeff R r f
)；∀ (x y : PiTensorProduct R fun i => s i), motive x → motive y → motive (x + y)
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.zero_tprodCoeff`：zero_tprodCoeff (f : Π i, s i) : tprodC
oeff R 0 f = 0
· 使用定理 `AddCon.induction_on`：∀ {M : Type u_1} [inst : Add M] {c : AddCon M} {C :
 c.Quotient → Prop} (q : c.Quotient), (∀ (x : M), C ↑x) → C q

--- 原说明 ---
Induct using `tprodCoeff`
-/
protected theorem induction_on' {motive : (⨂[R] i, s i) → Prop} (z : ⨂[R] i, s i)
    (tprodCoeff : ∀ (r : R) (f : Π i, s i), motive (tprodCoeff R r f))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z := by
  have C0 : motive 0 := by
    have h₁ := tprodCoeff 0 0
    rwa [zero_tprodCoeff] at h₁
  refine AddCon.induction_on z fun x ↦ FreeAddMonoid.recOn x C0 ?_
  simp_rw [AddCon.coe_add]
  refine fun f y ih ↦ add _ _ ?_ ih
  convert! tprodCoeff f.1 f.2

section DistribMulAction

variable [Monoid R₁] [DistribMulAction R₁ R] [SMulCommClass R₁ R R]
variable [Monoid R₂] [DistribMulAction R₂ R] [SMulCommClass R₂ R R]

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
/-
**PiTensorProduct.hasSMul'** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：hasSMul' : SMul R₁ (⨂[R] i, s i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasSMul' : SMul R₁ (⨂[R] i, s i) :=
  ⟨fun r ↦
    liftAddHom (fun f : R × Π i, s i ↦ tprodCoeff R (r • f.1) f.2)
      (fun r' f i hf ↦ by simp_rw [zero_tprodCoeff' _ f i hf])
      (fun f ↦ by simp [zero_tprodCoeff]) (fun r' f i m₁ m₂ ↦ by simp [add_tprodCoeff])
      (fun r' r'' f ↦ by simp [add_tprodCoeff']) fun z f i r' ↦ by
      simp [smul_tprodCoeff, mul_smul_comm]⟩
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (⨂[R] i, s i) :=
  PiTensorProduct.hasSMul'
/-
**PiTensorProduct.smul_tprodCoeff'** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：smul_tprodCoeff' (r : R₁) (z : R) (f : Π i, s i) : r • tprodCoeff R z f = 
tprodCoeff R (r • z) f
参数：r : R₁；z : R；f : Π i, s i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_tprodCoeff' (r : R₁) (z : R) (f : Π i, s i) :
    r • tprodCoeff R z f = tprodCoeff R (r • z) f := rfl
/-
**PiTensorProduct.smul_add** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {R₁ : Type u_5} {s
 : ι → Type u_7}   [inst_1 : (i : ι) → AddCommMonoid (s i)] [inst_2 : (i : ι) → 
_root_.Module R (s i)] [inst_3 : Monoid R₁]   [inst_4 : DistribMulAction R₁ R] [
inst_5 : SMulCommClass R₁ R R] (r : R₁) (x y : PiTensorProduct R fun i => s i), 
  r • (x + y) = r • x + r • y
参数：i : ι；s i；i : ι；s i；r : R₁；x y : PiTensorProduct R fun i => s i；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
protected theorem smul_add (r : R₁) (x y : ⨂[R] i, s i) : r • (x + y) = r • x + r • y :=
  map_add _ _ _
/-
**PiTensorProduct.distribMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：distribMulAction' : DistribMulAction R₁ (⨂[R] i, s i) where smul_add _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction' : DistribMulAction R₁ (⨂[R] i, s i) where
  smul_add _ _ _ := map_add _ _ _
  mul_smul r r' x :=
    PiTensorProduct.induction_on' x (fun {r'' f} ↦ by simp [smul_tprodCoeff', smul_smul])
      fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy]
  one_smul x :=
    PiTensorProduct.induction_on' x (fun {r f} ↦ by rw [smul_tprodCoeff', one_smul])
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]
  smul_zero _ := map_zero _
/-
**PiTensorProduct.smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：smulCommClass' [SMulCommClass R₁ R₂ R] : SMulCommClass R₁ R₂ (⨂[R] i, s i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.induction_on'`：∀ {ι : Type u_1} {R : Type u_4} [inst : C
ommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [in
st_2 : (i : ι) → _r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PiTensorProduct.smul_add`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSe
miring R] {R₁ : Type u_5} {s : ι → Type u_7}   [inst_1 : (i : ι) → AddCommMonoid
 (s i)] [inst_…
-/
instance smulCommClass' [SMulCommClass R₁ R₂ R] : SMulCommClass R₁ R₂ (⨂[R] i, s i) :=
  ⟨fun {r' r''} x ↦
    PiTensorProduct.induction_on' x (fun {xr xf} ↦ by simp only [smul_tprodCoeff', smul_comm])
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩
/-
**PiTensorProduct.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：isScalarTower' [SMul R₁ R₂] [IsScalarTower R₁ R₂ R] : IsScalarTower R₁ R₂ 
(⨂[R] i, s i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.induction_on'`：∀ {ι : Type u_1} {R : Type u_4} [inst : C
ommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [in
st_2 : (i : ι) → _r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PiTensorProduct.smul_add`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSe
miring R] {R₁ : Type u_5} {s : ι → Type u_7}   [inst_1 : (i : ι) → AddCommMonoid
 (s i)] [inst_…
-/
instance isScalarTower' [SMul R₁ R₂] [IsScalarTower R₁ R₂ R] :
    IsScalarTower R₁ R₂ (⨂[R] i, s i) :=
  ⟨fun {r' r''} x ↦
    PiTensorProduct.induction_on' x (fun {xr xf} ↦ by simp only [smul_tprodCoeff', smul_assoc])
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

end DistribMulAction

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
/-
**PiTensorProduct.module'** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：module' [Semiring R₁] [Module R₁ R] [SMulCommClass R₁ R R] : Module R₁ (⨂[
R] i, s i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module' [Semiring R₁] [Module R₁ R] [SMulCommClass R₁ R R] : Module R₁ (⨂[R] i, s i) :=
  { PiTensorProduct.distribMulAction' with
    add_smul := fun r r' x ↦
      PiTensorProduct.induction_on' x
        (fun {r f} ↦ by simp_rw [smul_tprodCoeff', add_smul, add_tprodCoeff'])
        fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_add_add_comm]
    zero_smul := fun x ↦
      PiTensorProduct.induction_on' x
        (fun {r f} ↦ by simp_rw [smul_tprodCoeff', zero_smul, zero_tprodCoeff])
        fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_zero] }

-- shortcut instances
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (⨂[R] i, s i) :=
  PiTensorProduct.module'
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass R R (⨂[R] i, s i) :=
  PiTensorProduct.smulCommClass'
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R R (⨂[R] i, s i) :=
  PiTensorProduct.isScalarTower'

variable (R) in
/-- The canonical `MultilinearMap R s (⨂[R] i, s i)`.

`tprod R fun i => f i` has notation `⨂ₜ[R] i, f i`. -/
/-
**PiTensorProduct.tprod** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：tprod : MultilinearMap R s (⨂[R] i, s i) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `MultilinearMap R s (⨂[R] i, s i)`.

`tprod R fun i => f i` has notation `⨂ₜ[R] i, f i`.
-/
def tprod : MultilinearMap R s (⨂[R] i, s i) where
  toFun := tprodCoeff R 1
  map_update_add' {_ f} i x y := (add_tprodCoeff (1 : R) f i x y).symm
  map_update_smul' {_ f} i r x := by
    rw [smul_tprodCoeff', ← smul_tprodCoeff (1 : R) _ i, update_idem, update_self]

@[inherit_doc tprod]
notation3:100 "⨂ₜ["R"] "(...)", "r:(scoped f => tprod R f) => r
/-
**PiTensorProduct.tprod_eq_tprodCoeff_one** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPro
duct`。
形式化陈述：tprod_eq_tprodCoeff_one : ⇑(tprod R : MultilinearMap R s (⨂[R] i, s i)) = 
tprodCoeff R 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tprod_eq_tprodCoeff_one :
    ⇑(tprod R : MultilinearMap R s (⨂[R] i, s i)) = tprodCoeff R 1 := rfl

@[simp]
/-
**PiTensorProduct.tprodCoeff_eq_smul_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPr
oduct`。
形式化陈述：tprodCoeff_eq_smul_tprod (z : R) (f : Π i, s i) : tprodCoeff R z f = z • t
prod R f
参数：z : R；f : Π i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tprodCoeff_eq_smul_tprod (z : R) (f : Π i, s i) : tprodCoeff R z f = z • tprod R f := by
  have : z = z • (1 : R) := by simp only [mul_one, smul_eq_mul]
  conv_lhs => rw [this]
  rfl

/-- The image of an element `p` of `FreeAddMonoid (R × Π i, s i)` in the `PiTensorProduct` is
equal to the sum of `a • ⨂ₜ[R] i, m i` over all the entries `(a, m)` of `p`.
-/
/-
**PiTensorProduct._root_.FreeAddMonoid.toPiTensorProduct** 是 Mathlib 中的一个引理，位于命名
空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of an element `p` of `FreeAddMonoid (R × Π i, s i)` in the `PiTensorPr
oduct` is
equal to the sum of `a • ⨂ₜ[R] i, m i` over all the entries `(a, m)` of `p`.
-/
lemma _root_.FreeAddMonoid.toPiTensorProduct (p : FreeAddMonoid (R × Π i, s i)) :
    AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p =
    List.sum (List.map (fun x ↦ x.1 • ⨂ₜ[R] i, x.2 i) p.toList) := by
  induction p using FreeAddMonoid.inductionOn' with
  | zero => rfl
  | of_add b a ih =>
    rw [FreeAddMonoid.toList_of_add, List.map_cons, List.sum_cons, ← ih, ← tprodCoeff_eq_smul_tprod]
    rfl

/-- The set of lifts of an element `x` of `⨂[R] i, s i` in `FreeAddMonoid (R × Π i, s i)`. -/
/-
**PiTensorProduct.lifts** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：lifts (x : ⨂[R] i, s i) : Set (FreeAddMonoid (R × Π i, s i))
参数：x : ⨂[R] i, s i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of lifts of an element `x` of `⨂[R] i, s i` in `FreeAddMonoid (R × Π i, 
s i)`.
-/
def lifts (x : ⨂[R] i, s i) : Set (FreeAddMonoid (R × Π i, s i)) :=
  {p | AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p = x}

set_option backward.isDefEq.respectTransparency false in
/-- An element `p` of `FreeAddMonoid (R × Π i, s i)` lifts an element `x` of `⨂[R] i, s i`
if and only if `x` is equal to the sum of `a • ⨂ₜ[R] i, m i` over all the entries
`(a, m)` of `p`.
-/
/-
**PiTensorProduct.mem_lifts_iff** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`。
形式化陈述：mem_lifts_iff (x : ⨂[R] i, s i) (p : FreeAddMonoid (R × Π i, s i)) : p in 
lifts x ↔ List.sum (List.map (fun x => x.1 • ⨂ₜ[R] i, x.2 i) p.toList) = x
参数：x : ⨂[R] i, s i；p : FreeAddMonoid (R × Π i, s i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FreeAddMonoid.toPiTensorProduct`：∀ {ι : Type u_1} {R : Type u_4} [inst :
 CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [
inst_2 : (i : ι) → _r…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An element `p` of `FreeAddMonoid (R × Π i, s i)` lifts an element `x` of `⨂[R] i
, s i`
if and only if `x` is equal to the sum of `a • ⨂ₜ[R] i, m i` over all the entrie
s
`(a, m)` of `p`.
-/
lemma mem_lifts_iff (x : ⨂[R] i, s i) (p : FreeAddMonoid (R × Π i, s i)) :
    p ∈ lifts x ↔ List.sum (List.map (fun x ↦ x.1 • ⨂ₜ[R] i, x.2 i) p.toList) = x := by
  simp only [lifts, Set.mem_ofPred_eq, FreeAddMonoid.toPiTensorProduct]

set_option backward.isDefEq.respectTransparency false in
/-- Every element of `⨂[R] i, s i` has a lift in `FreeAddMonoid (R × Π i, s i)`.
-/
/-
**PiTensorProduct.nonempty_lifts** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`。
形式化陈述：nonempty_lifts (x : ⨂[R] i, s i) : Set.Nonempty (lifts x)
参数：x : ⨂[R] i, s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Every element of `⨂[R] i, s i` has a lift in `FreeAddMonoid (R × Π i, s i)`.
-/
lemma nonempty_lifts (x : ⨂[R] i, s i) : Set.Nonempty (lifts x) := by
  existsi Quot.out x
  simp [lifts, ← AddCon.quot_mk_eq_coe]
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : ⨂[R] i, s i) : Nonempty ↑x.lifts := nonempty_subtype.mpr (nonempty_lifts x)

/-- The empty list lifts the element `0` of `⨂[R] i, s i`.
-/
/-
**PiTensorProduct.lifts_zero** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`。
形式化陈述：lifts_zero : 0 in lifts (0 : ⨂[R] i, s i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiTensorProduct.mem_lifts_iff`：mem_lifts_iff (x : ⨂[R] i, s i) (p : Free
AddMonoid (R × Π i, s i)) : p in lifts x ↔ List.sum (List.map (fun x => x.1 • ⨂ₜ
[R] i, x.2 i) p.toL…
· 使用定理 `FreeAddMonoid.toList_zero`：∀ {α : Type u_1}, FreeAddMonoid.toList 0 = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.sum_nil`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α], [].sum = 
0

--- 原说明 ---
The empty list lifts the element `0` of `⨂[R] i, s i`.
-/
lemma lifts_zero : 0 ∈ lifts (0 : ⨂[R] i, s i) := by
  rw [mem_lifts_iff, FreeAddMonoid.toList_zero, List.map_nil, List.sum_nil]

set_option backward.isDefEq.respectTransparency false in
/-- If elements `p,q` of `FreeAddMonoid (R × Π i, s i)` lift elements `x,y` of `⨂[R] i, s i`
respectively, then `p + q` lifts `x + y`.
-/
/-
**PiTensorProduct.lifts_add** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`。
形式化陈述：lifts_add {x y : ⨂[R] i, s i} {p q : FreeAddMonoid (R × Π i, s i)} (hp : p
 in lifts x) (hq : q in lifts y) : p + q in lifts (x + y)
参数：R × Π i, s i；hp : p in lifts x；hq : q in lifts y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If elements `p,q` of `FreeAddMonoid (R × Π i, s i)` lift elements `x,y` of `⨂[R]
 i, s i`
respectively, then `p + q` lifts `x + y`.
-/
lemma lifts_add {x y : ⨂[R] i, s i} {p q : FreeAddMonoid (R × Π i, s i)}
    (hp : p ∈ lifts x) (hq : q ∈ lifts y) : p + q ∈ lifts (x + y) := by
  simp only [lifts, Set.mem_ofPred_eq, AddCon.coe_add]
  rw [hp, hq]

/-- If an element `p` of `FreeAddMonoid (R × Π i, s i)` lifts an element `x` of `⨂[R] i, s i`,
and if `a` is an element of `R`, then the list obtained by multiplying the first entry of each
element of `p` by `a` lifts `a • x`.
-/
/-
**PiTensorProduct.lifts_smul** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`。
形式化陈述：lifts_smul {x : ⨂[R] i, s i} {p : FreeAddMonoid (R × Π i, s i)} (h : p in 
lifts x) (a : R) : p.map (fun (y : R × Π i, s i) => (a * y.1, y.2)) in lifts (a 
• x)
参数：R × Π i, s i；h : p in lifts x；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiTensorProduct.mem_lifts_iff`：mem_lifts_iff (x : ⨂[R] i, s i) (p : Free
AddMonoid (R × Π i, s i)) : p in lifts x ↔ List.sum (List.map (fun x => x.1 • ⨂ₜ
[R] i, x.2 i) p.toL…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `List.smul_sum`：List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (
r • ·)).sum
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If an element `p` of `FreeAddMonoid (R × Π i, s i)` lifts an element `x` of `⨂[R
] i, s i`,
and if `a` is an element of `R`, then the list obtained by multiplying the first
 entry of each
element of `p` by `a` lifts `a • x`.
-/
lemma lifts_smul {x : ⨂[R] i, s i} {p : FreeAddMonoid (R × Π i, s i)} (h : p ∈ lifts x) (a : R) :
    p.map (fun (y : R × Π i, s i) ↦ (a * y.1, y.2)) ∈ lifts (a • x) := by
  rw [mem_lifts_iff] at h ⊢
  rw [← h]
  simp [Function.comp_def, mul_smul, List.smul_sum]

/-- Induct using scaled versions of `PiTensorProduct.tprod`. -/
@[elab_as_elim]
/-
**PiTensorProduct.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {motive : (PiTensorProduct R fun i => s i) → Prop}   (z : PiTensorProduct
 R fun i => s i),   (∀ (r : R) (f : (i : ι) → s i), motive (r • (PiTensorProduct
.tprod R) f)) →     (∀ (x y : PiTensorProduct R fun i => s i), motive x → motive
 y → motive (x + y)) → motive z
参数：i : ι；s i；i : ι；s i；PiTensorProduct R fun i => s i；z : PiTensorProduct R fun 
i => s i；∀ (r : R) (f : (i : ι) → s i), motive (r • (PiTensorProduct.tprod R) f)
；∀ (x y : PiTensorProduct R fun i => s i), motive x → motive y → motive (x + y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.induction_on'`：∀ {ι : Type u_1} {R : Type u_4} [inst : C
ommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [in
st_2 : (i : ι) → _r…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Induct using scaled versions of `PiTensorProduct.tprod`.
-/
protected theorem induction_on {motive : (⨂[R] i, s i) → Prop} (z : ⨂[R] i, s i)
    (smul_tprod : ∀ (r : R) (f : Π i, s i), motive (r • tprod R f))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z := by
  simp_rw [← tprodCoeff_eq_smul_tprod] at smul_tprod
  exact PiTensorProduct.induction_on' z smul_tprod add

@[ext]
/-
**PiTensorProduct.ext** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMultilinearMap (tprod R) 
= φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
参数：⨂[R] i, s i；H : φ₁.compMultilinearMap (tprod R) = φ₂.compMultilinearMap (tpro
d R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `PiTensorProduct.induction_on'`：∀ {ι : Type u_1} {R : Type u_4} [inst : C
ommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [in
st_2 : (i : ι) → _r…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.tprodCoeff_eq_smul_tprod`：tprodCoeff_eq_smul_tprod (z : 
R) (f : Π i, s i) : tprodCoeff R z f = z • tprod R f
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MultilinearMap.congr_fun`：congr_fun {f g : MultilinearMap R M₁ M₂} (h : 
f = g) (x : forall i, M₁ i) : f x = g x
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem ext {φ₁ φ₂ : (⨂[R] i, s i) →ₗ[R] E}
    (H : φ₁.compMultilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂ := by
  refine LinearMap.ext ?_
  refine fun z ↦
    PiTensorProduct.induction_on' z ?_ fun {x y} hx hy ↦ by rw [φ₁.map_add, φ₂.map_add, hx, hy]
  · intro r f
    rw [tprodCoeff_eq_smul_tprod, φ₁.map_smul, φ₂.map_smul]
    apply congr_arg
    exact MultilinearMap.congr_fun H f

/-- The pure tensors (i.e. the elements of the image of `PiTensorProduct.tprod`) span
the tensor product. -/
/-
**PiTensorProduct.span_tprod_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：span_tprod_eq_top : Submodule.span R (Set.range (tprod R)) = (⊤ : Submodul
e R (⨂[R] i, s i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `PiTensorProduct.induction_on`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…

--- 原说明 ---
The pure tensors (i.e. the elements of the image of `PiTensorProduct.tprod`) spa
n
the tensor product.
-/
theorem span_tprod_eq_top :
    Submodule.span R (Set.range (tprod R)) = (⊤ : Submodule R (⨂[R] i, s i)) :=
  Submodule.eq_top_iff'.mpr fun t ↦ t.induction_on
    (fun _ _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (by simp only [Set.mem_range, exists_apply_eq_apply])))
    (fun _ _ hx hy ↦ Submodule.add_mem _ hx hy)

end Module

section Multilinear

open MultilinearMap

variable {s}

section lift

/-- Auxiliary function to constructing a linear map `(⨂[R] i, s i) → E` given a
`MultilinearMap R s E` with the property that its composition with the canonical
`MultilinearMap R s (⨂[R] i, s i)` is the given multilinear map. -/
/-
**PiTensorProduct.liftAux** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：liftAux (φ : MultilinearMap R s E) : (⨂[R] i, s i) ->+ E
参数：φ : MultilinearMap R s E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function to constructing a linear map `(⨂[R] i, s i) → E` given a
`MultilinearMap R s E` with the property that its composition with the canonical
`MultilinearMap R s (⨂[R] i, s i)` is the given multilinear map.
-/
def liftAux (φ : MultilinearMap R s E) : (⨂[R] i, s i) →+ E :=
  liftAddHom (fun p : R × Π i, s i ↦ p.1 • φ p.2)
    (fun z f i hf ↦ by simp_rw [map_coord_zero φ i hf, smul_zero])
    (fun f ↦ by simp_rw [zero_smul])
    (fun z f i m₁ m₂ ↦ by simp_rw [← smul_add, φ.map_update_add])
    (fun z₁ z₂ f ↦ by rw [← add_smul])
    fun z f i r ↦ by simp [φ.map_update_smul, smul_smul, mul_comm]
/-
**PiTensorProduct.liftAux_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：liftAux_tprod (φ : MultilinearMap R s E) (f : Π i, s i) : liftAux φ (tprod
 R f) = φ f
参数：φ : MultilinearMap R s E；f : Π i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.lift_coe`：∀ {M : Type u_1} {P : Type u_3} [inst : AddZeroClass M]
 [inst_1 : AddZeroClass P] {c : AddCon M} {f : M →+ P}   (H : c ≤ AddCon.ker f) 
(x : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftAux_tprod (φ : MultilinearMap R s E) (f : Π i, s i) : liftAux φ (tprod R f) = φ f := by
  simp only [liftAux, liftAddHom, tprod_eq_tprodCoeff_one, tprodCoeff, AddCon.coe_mk']
  -- The end of this proof was very different before https://github.com/leanprover/lean4/pull/2644:
  -- rw [FreeAddMonoid.of, FreeAddMonoid.ofList, Equiv.refl_apply, AddCon.lift_coe]
  -- dsimp [FreeAddMonoid.lift, FreeAddMonoid.sumAux]
  -- show _ • _ = _
  -- rw [one_smul]
  conv_lhs => apply AddCon.lift_coe
  simp
/-
**PiTensorProduct.liftAux_tprodCoeff** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`
。
形式化陈述：liftAux_tprodCoeff (φ : MultilinearMap R s E) (z : R) (f : Π i, s i) : lif
tAux φ (tprodCoeff R z f) = z • φ f
参数：φ : MultilinearMap R s E；z : R；f : Π i, s i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAux_tprodCoeff (φ : MultilinearMap R s E) (z : R) (f : Π i, s i) :
    liftAux φ (tprodCoeff R z f) = z • φ f := rfl
/-
**PiTensorProduct.liftAux.smul** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct.liftAu
x`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {E : Type u_9} [inst_3 : AddCommMonoid E] [inst_4 : _root_.Module R E]   
{φ : MultilinearMap R s E} (r : R) (x : PiTensorProduct R fun i => s i),   (PiTe
nsorProduct.liftAux φ) (r • x) = r • (PiTensorProduct.liftAux φ) x
参数：i : ι；s i；i : ι；s i；r : R；x : PiTensorProduct R fun i => s i；PiTensorProduct.
liftAux φ；r • x；PiTensorProduct.liftAux φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.induction_on'`：∀ {ι : Type u_1} {R : Type u_4} [inst : C
ommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [in
st_2 : (i : ι) → _r…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PiTensorProduct.smul_tprodCoeff'`：smul_tprodCoeff' (r : R₁) (z : R) (f :
 Π i, s i) : r • tprodCoeff R z f = tprodCoeff R (r • z) f
· 使用定理 `PiTensorProduct.liftAux_tprodCoeff`：liftAux_tprodCoeff (φ : MultilinearM
ap R s E) (z : R) (f : Π i, s i) : liftAux φ (tprodCoeff R z f) = z • φ f
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
-/
theorem liftAux.smul {φ : MultilinearMap R s E} (r : R) (x : ⨂[R] i, s i) :
    liftAux φ (r • x) = r • liftAux φ x := by
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro z f
    rw [smul_tprodCoeff' r z f, liftAux_tprodCoeff, liftAux_tprodCoeff, smul_assoc]
  · intro z y ihz ihy
    rw [smul_add, (liftAux φ).map_add, ihz, ihy, (liftAux φ).map_add, smul_add]

/-- Constructing a linear map `(⨂[R] i, s i) → E` given a `MultilinearMap R s E` with the
property that its composition with the canonical `MultilinearMap R s E` is
the given multilinear map `φ`. -/
/-
**PiTensorProduct.lift** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：lift : MultilinearMap R s E ≃ₗ[R] (⨂[R] i, s i) ->ₗ[R] E where toFun φ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.liftAux.smul`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…

--- 原说明 ---
Constructing a linear map `(⨂[R] i, s i) → E` given a `MultilinearMap R s E` wit
h the
property that its composition with the canonical `MultilinearMap R s E` is
the given multilinear map `φ`.
-/
def lift : MultilinearMap R s E ≃ₗ[R] (⨂[R] i, s i) →ₗ[R] E where
  toFun φ := { liftAux φ with map_smul' := liftAux.smul }
  invFun φ' := φ'.compMultilinearMap (tprod R)
  left_inv φ := by
    ext
    simp [liftAux_tprod, LinearMap.compMultilinearMap]
  right_inv φ := by
    ext
    simp [liftAux_tprod]
  map_add' φ₁ φ₂ := by
    ext
    simp [liftAux_tprod]
  map_smul' r φ₂ := by
    ext
    simp [liftAux_tprod]

variable {φ : MultilinearMap R s E}

@[simp]
/-
**PiTensorProduct.lift.tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct.lift`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {E : Type u_9} [inst_3 : AddCommMonoid E] [inst_4 : _root_.Module R E]   
{φ : MultilinearMap R s E} (f : (i : ι) → s i), (PiTensorProduct.lift φ) ((PiTen
sorProduct.tprod R) f) = φ f
参数：i : ι；s i；i : ι；s i；f : (i : ι) → s i；PiTensorProduct.lift φ；(PiTensorProduct
.tprod R) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.liftAux_tprod`：liftAux_tprod (φ : MultilinearMap R s E) 
(f : Π i, s i) : liftAux φ (tprod R f) = φ f
-/
theorem lift.tprod (f : Π i, s i) : lift φ (tprod R f) = φ f :=
  liftAux_tprod φ f
/-
**PiTensorProduct.lift.unique'** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct.lift`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {E : Type u_9} [inst_3 : AddCommMonoid E] [inst_4 : _root_.Module R E]   
{φ : MultilinearMap R s E} {φ' : (PiTensorProduct R fun i => s i) →ₗ[R] E},   φ'
.compMultilinearMap (PiTensorProduct.tprod R) = φ → φ' = PiTensorProduct.lift φ
参数：i : ι；s i；i : ι；s i；PiTensorProduct R fun i => s i；PiTensorProduct.tprod R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem lift.unique' {φ' : (⨂[R] i, s i) →ₗ[R] E}
    (H : φ'.compMultilinearMap (PiTensorProduct.tprod R) = φ) : φ' = lift φ :=
  ext <| H.symm ▸ (lift.symm_apply_apply φ).symm
/-
**PiTensorProduct.lift.unique** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct.lift`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {E : Type u_9} [inst_3 : AddCommMonoid E] [inst_4 : _root_.Module R E]   
{φ : MultilinearMap R s E} {φ' : (PiTensorProduct R fun i => s i) →ₗ[R] E},   (∀
 (f : (i : ι) → s i), φ' ((PiTensorProduct.tprod R) f) = φ f) → φ' = PiTensorPro
duct.lift φ
参数：i : ι；s i；i : ι；s i；PiTensorProduct R fun i => s i；∀ (f : (i : ι) → s i), φ' 
((PiTensorProduct.tprod R) f) = φ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.lift.unique'`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
-/
theorem lift.unique {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : ∀ f, φ' (PiTensorProduct.tprod R f) = φ f) :
    φ' = lift φ :=
  lift.unique' (MultilinearMap.ext H)

@[simp]
/-
**PiTensorProduct.lift_symm** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：lift_symm (φ' : (⨂[R] i, s i) ->ₗ[R] E) : lift.symm φ' = φ'.compMultilinea
rMap (tprod R)
参数：φ' : (⨂[R] i, s i) ->ₗ[R] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_symm (φ' : (⨂[R] i, s i) →ₗ[R] E) : lift.symm φ' = φ'.compMultilinearMap (tprod R) :=
  rfl

@[simp]
/-
**PiTensorProduct.lift_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：lift_tprod : lift (tprod R : MultilinearMap R s _) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiTensorProduct.lift.unique'`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…
-/
theorem lift_tprod : lift (tprod R : MultilinearMap R s _) = LinearMap.id :=
  Eq.symm <| lift.unique' rfl

end lift

section map

variable {t t' : ι → Type*}
variable [∀ i, AddCommMonoid (t i)] [∀ i, Module R (t i)]
variable [∀ i, AddCommMonoid (t' i)] [∀ i, Module R (t' i)]
variable (g : Π i, t i →ₗ[R] t' i) (f : Π i, s i →ₗ[R] t i)

/--
Let `sᵢ` and `tᵢ` be two families of `R`-modules.
Let `f` be a family of `R`-linear maps between `sᵢ` and `tᵢ`, i.e. `f : Πᵢ sᵢ → tᵢ`,
then there is an induced map `⨂ᵢ sᵢ → ⨂ᵢ tᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`.

This is `TensorProduct.map` for an arbitrary family of modules.
-/
/-
**PiTensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：map : (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `sᵢ` and `tᵢ` be two families of `R`-modules.
Let `f` be a family of `R`-linear maps between `sᵢ` and `tᵢ`, i.e. `f : Πᵢ sᵢ → 
tᵢ`,
then there is an induced map `⨂ᵢ sᵢ → ⨂ᵢ tᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`.

This is `TensorProduct.map` for an arbitrary family of modules.
-/
def map : (⨂[R] i, s i) →ₗ[R] ⨂[R] i, t i :=
  lift <| (tprod R).compLinearMap f
/-
**PiTensorProduct.map_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {t : ι → Type u_11} [inst_3 : (i : ι) → AddCommMonoid (t i)]   [inst_4 : 
(i : ι) → _root_.Module R (t i)] (f : (i : ι) → s i →ₗ[R] t i) (x : (i : ι) → s 
i),   (PiTensorProduct.map f) ((PiTensorProduct.tprod R) x) = ⨂ₜ[R] (i : ι), (f 
i) (x i)
参数：i : ι；s i；i : ι；s i；i : ι；t i；i : ι；t i；f : (i : ι) → s i →ₗ[R] t i；x : (i : 
ι) → s i；PiTensorProduct.map f；(PiTensorProduct.tprod R) x；i : ι；f i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
-/
@[simp] lemma map_tprod (x : Π i, s i) :
    map f (tprod R x) = tprod R fun i ↦ f i (x i) :=
  lift.tprod _

-- No lemmas about associativity, because we don't have associativity of `PiTensorProduct` yet.
/-
**PiTensorProduct.map_range_eq_span_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPro
duct`。
形式化陈述：map_range_eq_span_tprod : LinearMap.range (map f) = Submodule.span R {t | 
exists (m : Π i, s i), tprod R (fun i => f i (m i)) = t}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `PiTensorProduct.span_tprod_eq_top`：span_tprod_eq_top : Submodule.span R 
(Set.range (tprod R)) = (⊤ : Submodule R (⨂[R] i, s i))
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_range_eq_span_tprod :
    LinearMap.range (map f) =
      Submodule.span R {t | ∃ (m : Π i, s i), tprod R (fun i ↦ f i (m i)) = t} := by
  rw [← Submodule.map_top, ← span_tprod_eq_top, Submodule.map_span, ← Set.range_comp]
  apply congrArg; ext x
  simp only [Set.mem_range, comp_apply, map_tprod, Set.mem_ofPred_eq]

/-- Given submodules `p i ⊆ s i`, this is the natural map: `⨂[R] i, p i → ⨂[R] i, s i`.
This is `TensorProduct.mapIncl` for an arbitrary family of modules.
-/
@[simp]
/-
**PiTensorProduct.mapIncl** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：mapIncl (p : Π i, Submodule R (s i)) : (⨂[R] i, p i) ->ₗ[R] ⨂[R] i, s i
参数：p : Π i, Submodule R (s i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given submodules `p i ⊆ s i`, this is the natural map: `⨂[R] i, p i → ⨂[R] i, s 
i`.
This is `TensorProduct.mapIncl` for an arbitrary family of modules.
-/
def mapIncl (p : Π i, Submodule R (s i)) : (⨂[R] i, p i) →ₗ[R] ⨂[R] i, s i :=
  map fun (i : ι) ↦ (p i).subtype
/-
**PiTensorProduct.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：map_comp : map (fun (i : ι) => g i ∘ₗ f i) = map g ∘ₗ map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp : map (fun (i : ι) ↦ g i ∘ₗ f i) = map g ∘ₗ map f := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.coe_comp, Function.comp_apply]
/-
**PiTensorProduct.lift_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：lift_comp_map (h : MultilinearMap R t E) : lift h ∘ₗ map f = lift (h.compL
inearMap f)
参数：h : MultilinearMap R t E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_map (h : MultilinearMap R t E) :
    lift h ∘ₗ map f = lift (h.compLinearMap f) := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    map_tprod, lift.tprod, MultilinearMap.compLinearMap_apply]

attribute [local ext high] ext

@[simp]
/-
**PiTensorProduct.map_id** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：map_id : map (fun i => (LinearMap.id : s i ->ₗ[R] s i)) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id : map (fun i ↦ (LinearMap.id : s i →ₗ[R] s i)) = .id := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.id_coe, id_eq]

@[simp]
/-
**PiTensorProduct.map_one** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)], (PiTensorProduct.map fun i => 1) = 1
参数：i : ι；s i；i : ι；s i；PiTensorProduct.map fun i => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.map_id`：map_id : map (fun i => (LinearMap.id : s i ->ₗ[R
] s i)) = .id
-/
protected theorem map_one : map (fun (i : ι) ↦ (1 : s i →ₗ[R] s i)) = 1 :=
  map_id
/-
**PiTensorProduct.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] (f₁ f₂ : (i : ι) → s i →ₗ[R] s i),   (PiTensorProduct.map fun i => f₁ i *
 f₂ i) = PiTensorProduct.map f₁ * PiTensorProduct.map f₂
参数：i : ι；s i；i : ι；s i；f₁ f₂ : (i : ι) → s i →ₗ[R] s i；PiTensorProduct.map fun i
 => f₁ i * f₂ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.map_comp`：map_comp : map (fun (i : ι) => g i ∘ₗ f i) = m
ap g ∘ₗ map f
-/
protected theorem map_mul (f₁ f₂ : Π i, s i →ₗ[R] s i) :
    map (fun i ↦ f₁ i * f₂ i) = map f₁ * map f₂ :=
  map_comp f₁ f₂

/-- Upgrading `PiTensorProduct.map` to a `MonoidHom` when `s = t`. -/
@[simps]
/-
**PiTensorProduct.mapMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：mapMonoidHom : (Π i, s i ->ₗ[R] s i) ->* ((⨂[R] i, s i) ->ₗ[R] ⨂[R] i, s i
) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.map_one`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSem
iring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 :
 (i : ι) → _r…
· 使用定理 `PiTensorProduct.map_mul`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSem
iring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 :
 (i : ι) → _r…

--- 原说明 ---
Upgrading `PiTensorProduct.map` to a `MonoidHom` when `s = t`.
-/
def mapMonoidHom : (Π i, s i →ₗ[R] s i) →* ((⨂[R] i, s i) →ₗ[R] ⨂[R] i, s i) where
  toFun := map
  map_one' := PiTensorProduct.map_one
  map_mul' := PiTensorProduct.map_mul

@[simp]
/-
**PiTensorProduct.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] (f : (i : ι) → s i →ₗ[R] s i) (n : ℕ),   PiTensorProduct.map (f ^ n) = Pi
TensorProduct.map f ^ n
参数：i : ι；s i；i : ι；s i；f : (i : ι) → s i →ₗ[R] s i；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
protected theorem map_pow (f : Π i, s i →ₗ[R] s i) (n : ℕ) :
    map (f ^ n) = map f ^ n := map_pow mapMonoidHom _ _

open Function in
/-
**PiTensorProduct.map_add_smul_aux** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem map_add_smul_aux [DecidableEq ι] (i : ι) (x : Π i, s i) (u : s i →ₗ[R] t i) :
    (fun j ↦ update f i u j (x j)) = update (fun j ↦ (f j) (x j)) i (u (x i)) := by
  ext j
  exact apply_update (fun i F => F (x i)) f i u j

open Function in
/-
**PiTensorProduct.map_update_add** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {t : ι → Type u_11} [inst_3 : (i : ι) → AddCommMonoid (t i)]   [inst_4 : 
(i : ι) → _root_.Module R (t i)] (f : (i : ι) → s i →ₗ[R] t i) [inst_5 : Decidab
leEq ι] (i : ι)   (u v : s i →ₗ[R] t i),   PiTensorProduct.map (Function.update 
f i (u + v)) =     PiTensorProduct.map (Function.update f i u) + PiTensorProduct
.map (Function.update f i v)
参数：i : ι；s i；i : ι；s i；i : ι；t i；i : ι；t i；f : (i : ι) → s i →ₗ[R] t i；i : ι；u v
 : s i →ₗ[R] t i；Function.update f i (u + v)；Function.update f i u；Function.upda
te f i v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `_private.Mathlib.LinearAlgebra.PiTensorProduct.Basic.0.PiTensorProduct.m
ap_add_smul_aux`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι 
→ Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_update_add [DecidableEq ι] (i : ι) (u v : s i →ₗ[R] t i) :
    map (update f i (u + v)) = map (update f i u) + map (update f i v) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.add_apply,
    MultilinearMap.map_update_add]

open Function in
/-
**PiTensorProduct.map_update_smul** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {t : ι → Type u_11} [inst_3 : (i : ι) → AddCommMonoid (t i)]   [inst_4 : 
(i : ι) → _root_.Module R (t i)] (f : (i : ι) → s i →ₗ[R] t i) [inst_5 : Decidab
leEq ι] (i : ι) (c : R)   (u : s i →ₗ[R] t i),   PiTensorProduct.map (Function.u
pdate f i (c • u)) = c • PiTensorProduct.map (Function.update f i u)
参数：i : ι；s i；i : ι；s i；i : ι；t i；i : ι；t i；f : (i : ι) → s i →ₗ[R] t i；i : ι；c :
 R；u : s i →ₗ[R] t i；Function.update f i (c • u)；Function.update f i u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `_private.Mathlib.LinearAlgebra.PiTensorProduct.Basic.0.PiTensorProduct.m
ap_add_smul_aux`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι 
→ Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.map_update_smul`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_update_smul [DecidableEq ι] (i : ι) (c : R) (u : s i →ₗ[R] t i) :
    map (update f i (c • u)) = c • map (update f i u) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.smul_apply,
    MultilinearMap.map_update_smul]

variable (R s t)

/-- The tensor of a family of linear maps from `sᵢ` to `tᵢ`, as a multilinear map of
the family.
-/
@[simps]
/-
**PiTensorProduct.mapMultilinear** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：mapMultilinear : MultilinearMap R (fun (i : ι) => s i ->ₗ[R] t i) ((⨂[R] i
, s i) ->ₗ[R] ⨂[R] i, t i) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.map_update_add`：∀ {ι : Type u_1} {R : Type u_4} [inst : 
CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [i
nst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.map_update_smul`：∀ {ι : Type u_1} {R : Type u_4} [inst :
 CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [
inst_2 : (i : ι) → _r…

--- 原说明 ---
The tensor of a family of linear maps from `sᵢ` to `tᵢ`, as a multilinear map of
the family.
-/
noncomputable def mapMultilinear :
    MultilinearMap R (fun (i : ι) ↦ s i →ₗ[R] t i) ((⨂[R] i, s i) →ₗ[R] ⨂[R] i, t i) where
  toFun := map
  map_update_smul' _ _ _ _ := PiTensorProduct.map_update_smul _ _ _ _
  map_update_add' _ _ _ _ := PiTensorProduct.map_update_add _ _ _ _

variable {R s t}

/--
Let `sᵢ` and `tᵢ` be families of `R`-modules.
Then there is an `R`-linear map between `⨂ᵢ Hom(sᵢ, tᵢ)` and `Hom(⨂ᵢ sᵢ, ⨂ tᵢ)` defined by
`⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ fᵢ aᵢ`.

This is `TensorProduct.homTensorHomMap` for an arbitrary family of modules.

Note that `PiTensorProduct.piTensorHomMap (tprod R f)` is equal to `PiTensorProduct.map f`.
-/
/-
**PiTensorProduct.piTensorHomMap** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：piTensorHomMap : (⨂[R] i, s i ->ₗ[R] t i) ->ₗ[R] (⨂[R] i, s i) ->ₗ[R] ⨂[R]
 i, t i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…

--- 原说明 ---
Let `sᵢ` and `tᵢ` be families of `R`-modules.
Then there is an `R`-linear map between `⨂ᵢ Hom(sᵢ, tᵢ)` and `Hom(⨂ᵢ sᵢ, ⨂ tᵢ)` 
defined by
`⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ fᵢ aᵢ`.

This is `TensorProduct.homTensorHomMap` for an arbitrary family of modules.

Note that `PiTensorProduct.piTensorHomMap (tprod R f)` is equal to `PiTensorProd
uct.map f`.
-/
def piTensorHomMap : (⨂[R] i, s i →ₗ[R] t i) →ₗ[R] (⨂[R] i, s i) →ₗ[R] ⨂[R] i, t i :=
  lift.toLinearMap ∘ₗ lift (MultilinearMap.piLinearMap <| tprod R)
/-
**PiTensorProduct.piTensorHomMap_tprod_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensor
Product`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7}
 [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _root_.Module R 
(s i)] {t : ι → Type u_11} [inst_3 : (i : ι) → AddCommMonoid (t i)]   [inst_4 : 
(i : ι) → _root_.Module R (t i)] (f : (i : ι) → s i →ₗ[R] t i) (x : (i : ι) → s 
i),   (PiTensorProduct.piTensorHomMap ((PiTensorProduct.tprod R) f)) ((PiTensorP
roduct.tprod R) x) =     ⨂ₜ[R] (i : ι), (f i) (x i)
参数：i : ι；s i；i : ι；s i；i : ι；t i；i : ι；t i；f : (i : ι) → s i →ₗ[R] t i；x : (i : 
ι) → s i；PiTensorProduct.piTensorHomMap ((PiTensorProduct.tprod R) f)；(PiTensorP
roduct.tprod R) x；i : ι；f i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.piLinearMap_apply_apply_apply`：∀ {R : Type uR} {ι : Type 
uι} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₂ : Type v₂} [inst : CommSemiring 
R]   [inst_1 : (i : ι) → AddCommMo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma piTensorHomMap_tprod_tprod (f : Π i, s i →ₗ[R] t i) (x : Π i, s i) :
    piTensorHomMap (tprod R f) (tprod R x) = tprod R fun i ↦ f i (x i) := by
  simp [piTensorHomMap]
/-
**PiTensorProduct.piTensorHomMap_tprod_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `PiTenso
rProduct`。
形式化陈述：piTensorHomMap_tprod_eq_map (f : Π i, s i ->ₗ[R] t i) : piTensorHomMap (tp
rod R f) = map f
参数：f : Π i, s i ->ₗ[R] t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.piTensorHomMap_tprod_tprod`：∀ {ι : Type u_1} {R : Type u
_4} [inst : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid
 (s i)]   [inst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piTensorHomMap_tprod_eq_map (f : Π i, s i →ₗ[R] t i) :
    piTensorHomMap (tprod R f) = map f := by
  ext; simp

/-- If `s i` and `t i` are linearly equivalent for every `i` in `ι`, then `⨂[R] i, s i` and
`⨂[R] i, t i` are linearly equivalent.

This is the n-ary version of `TensorProduct.congr`
-/
/-
**PiTensorProduct.congr** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：congr (f : Π i, s i ≃ₗ[R] t i) : (⨂[R] i, s i) ≃ₗ[R] ⨂[R] i, t i
参数：f : Π i, s i ≃ₗ[R] t i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s i` and `t i` are linearly equivalent for every `i` in `ι`, then `⨂[R] i, s
 i` and
`⨂[R] i, t i` are linearly equivalent.

This is the n-ary version of `TensorProduct.congr`
-/
noncomputable def congr (f : Π i, s i ≃ₗ[R] t i) :
    (⨂[R] i, s i) ≃ₗ[R] ⨂[R] i, t i :=
  .ofLinearMap
    (map (fun i ↦ f i))
    (map (fun i ↦ (f i).symm))
    (by ext; simp)
    (by ext; simp)

@[simp]
/-
**PiTensorProduct.congr_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：congr_tprod (f : Π i, s i ≃ₗ[R] t i) (m : Π i, s i) : congr f (tprod R m) 
= tprod R (fun (i : ι) => (f i) (m i))
参数：f : Π i, s i ≃ₗ[R] t i；m : Π i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem congr_tprod (f : Π i, s i ≃ₗ[R] t i) (m : Π i, s i) :
    congr f (tprod R m) = tprod R (fun (i : ι) ↦ (f i) (m i)) := by
  simp only [congr, LinearEquiv.coe_ofLinearMap, map_tprod, LinearEquiv.coe_coe]

@[simp]
/-
**PiTensorProduct.congr_symm_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：congr_symm_tprod (f : Π i, s i ≃ₗ[R] t i) (p : Π i, t i) : (congr f).symm 
(tprod R p) = tprod R (fun (i : ι) => (f i).symm (p i))
参数：f : Π i, s i ≃ₗ[R] t i；p : Π i, t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem congr_symm_tprod (f : Π i, s i ≃ₗ[R] t i) (p : Π i, t i) :
    (congr f).symm (tprod R p) = tprod R (fun (i : ι) ↦ (f i).symm (p i)) := by
  simp only [congr, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap, map_tprod,
    LinearEquiv.coe_coe]

/--
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules, then `f : Πᵢ sᵢ → tᵢ → t'ᵢ` induces an
element of `Hom(⨂ᵢ sᵢ, Hom(⨂ tᵢ, ⨂ᵢ t'ᵢ))` defined by `⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`.

This is `PiTensorProduct.map` for two arbitrary families of modules.
This is `TensorProduct.map₂` for families of modules.
-/
/-
**PiTensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：map : (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules, then `f : Πᵢ sᵢ → tᵢ → t'ᵢ`
 induces an
element of `Hom(⨂ᵢ sᵢ, Hom(⨂ tᵢ, ⨂ᵢ t'ᵢ))` defined by `⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ 
bᵢ`.

This is `PiTensorProduct.map` for two arbitrary families of modules.
This is `TensorProduct.map₂` for families of modules.
-/
def map₂ (f : Π i, s i →ₗ[R] t i →ₗ[R] t' i) :
    (⨂[R] i, s i) →ₗ[R] (⨂[R] i, t i) →ₗ[R] ⨂[R] i, t' i :=
  lift <| LinearMap.compMultilinearMap piTensorHomMap <| (tprod R).compLinearMap f
/-
**PiTensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：map : (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_tprod_tprod (f : Π i, s i →ₗ[R] t i →ₗ[R] t' i) (x : Π i, s i) (y : Π i, t i) :
    map₂ f (tprod R x) (tprod R y) = tprod R fun i ↦ f i (x i) (y i) := by
  simp [map₂]

/--
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules.
Then there is a function from `⨂ᵢ Hom(sᵢ, Hom(tᵢ, t'ᵢ))` to `Hom(⨂ᵢ sᵢ, Hom(⨂ tᵢ, ⨂ᵢ t'ᵢ))`
defined by `⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`. -/
/-
**PiTensorProduct.piTensorHomMapFun** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules.
Then there is a function from `⨂ᵢ Hom(sᵢ, Hom(tᵢ, t'ᵢ))` to `Hom(⨂ᵢ sᵢ, Hom(⨂ tᵢ
, ⨂ᵢ t'ᵢ))`
defined by `⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`.
-/
def piTensorHomMapFun₂ : (⨂[R] i, s i →ₗ[R] t i →ₗ[R] t' i) →
    (⨂[R] i, s i) →ₗ[R] (⨂[R] i, t i) →ₗ[R] (⨂[R] i, t' i) :=
  fun φ => lift <| LinearMap.compMultilinearMap piTensorHomMap <|
    (lift <| MultilinearMap.piLinearMap <| tprod R) φ
/-
**PiTensorProduct.piTensorHomMapFun** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piTensorHomMapFun₂_add (φ ψ : ⨂[R] i, s i →ₗ[R] t i →ₗ[R] t' i) :
    piTensorHomMapFun₂ (φ + ψ) = piTensorHomMapFun₂ φ + piTensorHomMapFun₂ ψ := by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_add, LinearMap.compMultilinearMap_apply,
    lift.tprod, add_apply, LinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**PiTensorProduct.piTensorHomMapFun** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piTensorHomMapFun₂_smul (r : R) (φ : ⨂[R] i, s i →ₗ[R] t i →ₗ[R] t' i) :
    piTensorHomMapFun₂ (r • φ) = r • piTensorHomMapFun₂ φ := by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_smul, LinearMap.compMultilinearMap_apply,
    lift.tprod, smul_apply, LinearMap.smul_apply]

/--
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules.
Then there is a linear map from `⨂ᵢ Hom(sᵢ, Hom(tᵢ, t'ᵢ))` to `Hom(⨂ᵢ sᵢ, Hom(⨂ tᵢ, ⨂ᵢ t'ᵢ))`
defined by `⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`.

This is `TensorProduct.homTensorHomMap` for two arbitrary families of modules.
-/
/-
**PiTensorProduct.piTensorHomMap** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：piTensorHomMap : (⨂[R] i, s i ->ₗ[R] t i) ->ₗ[R] (⨂[R] i, s i) ->ₗ[R] ⨂[R]
 i, t i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…

--- 原说明 ---
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules.
Then there is a linear map from `⨂ᵢ Hom(sᵢ, Hom(tᵢ, t'ᵢ))` to `Hom(⨂ᵢ sᵢ, Hom(⨂ 
tᵢ, ⨂ᵢ t'ᵢ))`
defined by `⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`.

This is `TensorProduct.homTensorHomMap` for two arbitrary families of modules.
-/
def piTensorHomMap₂ : (⨂[R] i, s i →ₗ[R] t i →ₗ[R] t' i) →ₗ[R]
    (⨂[R] i, s i) →ₗ[R] (⨂[R] i, t i) →ₗ[R] (⨂[R] i, t' i) where
  toFun := piTensorHomMapFun₂
  map_add' x y := piTensorHomMapFun₂_add x y
  map_smul' x y := piTensorHomMapFun₂_smul x y

set_option backward.isDefEq.respectTransparency false in
/-
**PiTensorProduct.piTensorHomMap** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：piTensorHomMap : (⨂[R] i, s i ->ₗ[R] t i) ->ₗ[R] (⨂[R] i, s i) ->ₗ[R] ⨂[R]
 i, t i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
-/
@[simp] lemma piTensorHomMap₂_tprod_tprod_tprod
    (f : ∀ i, s i →ₗ[R] t i →ₗ[R] t' i) (a : ∀ i, s i) (b : ∀ i, t i) :
    piTensorHomMap₂ (tprod R f) (tprod R a) (tprod R b) = tprod R (fun i ↦ f i (a i) (b i)) := by
  simp [piTensorHomMapFun₂, piTensorHomMap₂]

end map

section

variable (R M)

variable (s) in
/-- Re-index the components of the tensor power by `e`. -/
/-
**PiTensorProduct.reindex** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：reindex (e : ι ≃ ι₂) : (⨂[R] i : ι, s i) ≃ₗ[R] ⨂[R] i : ι₂, s (e.symm i)
参数：e : ι ≃ ι₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…

--- 原说明 ---
Re-index the components of the tensor power by `e`.
-/
def reindex (e : ι ≃ ι₂) : (⨂[R] i : ι, s i) ≃ₗ[R] ⨂[R] i : ι₂, s (e.symm i) :=
  let f := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι₂), s (e.symm i)) e
  let g := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι), s i) e
  LinearEquiv.ofLinearMap (lift <| f.symm <| tprod R) (lift <| g <| tprod R) (by aesop) (by aesop)

end

@[simp]
/-
**PiTensorProduct.reindex_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i) : reindex R s e (tprod R f) = tp
rod R fun i => f (e.symm i)
参数：e : ι ≃ ι₂；f : Π i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PiTensorProduct.liftAux_tprod`：liftAux_tprod (φ : MultilinearMap R s E) 
(f : Π i, s i) : liftAux φ (tprod R f) = φ f
-/
theorem reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i) :
    reindex R s e (tprod R f) = tprod R fun i ↦ f (e.symm i) := by
  dsimp [reindex]
  exact liftAux_tprod _ f

@[simp]
/-
**PiTensorProduct.reindex_comp_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`
。
形式化陈述：reindex_comp_tprod (e : ι ≃ ι₂) : (reindex R s e).compMultilinearMap (tpro
d R) = (domDomCongrLinearEquiv' R R s _ e).symm (tprod R)
参数：e : ι ≃ ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.reindex_tprod`：reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i)
 : reindex R s e (tprod R f) = tprod R fun i => f (e.symm i)
-/
theorem reindex_comp_tprod (e : ι ≃ ι₂) :
    (reindex R s e).compMultilinearMap (tprod R) =
    (domDomCongrLinearEquiv' R R s _ e).symm (tprod R) :=
  MultilinearMap.ext <| reindex_tprod e
/-
**PiTensorProduct.lift_comp_reindex** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：lift_comp_reindex (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i => s (e.symm i
)) E) : lift φ ∘ₗ (reindex R s e) = lift ((domDomCongrLinearEquiv' R R s _ e).sy
mm φ)
参数：e : ι ≃ ι₂；φ : MultilinearMap R (fun i => s (e.symm i)) E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.domDomCongrLinearEquiv'_apply`：∀ (R : Type uR) (S : Type 
uS) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [inst : Semiring R]   [inst_
1 : (i : ι) → AddCommMonoid (M₁ i)…
· 使用定理 `MultilinearMap.domDomCongrLinearEquiv'_symm_apply`：∀ (R : Type uR) (S : 
Type uS) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [inst : Semiring R]   [
inst_1 : (i : ι) → AddCommMonoid (M₁ i)…
· 使用定理 `LinearEquiv.ofLinearMap.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M 
: Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] [ins…
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_reindex (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i ↦ s (e.symm i)) E) :
    lift φ ∘ₗ (reindex R s e) = lift ((domDomCongrLinearEquiv' R R s _ e).symm φ) := by
  ext; simp [reindex]

@[simp]
/-
**PiTensorProduct.lift_comp_reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProd
uct`。
形式化陈述：lift_comp_reindex_symm (e : ι ≃ ι₂) (φ : MultilinearMap R s E) : lift φ ∘ₗ
 (reindex R s e).symm = lift (domDomCongrLinearEquiv' R R s _ e φ)
参数：e : ι ≃ ι₂；φ : MultilinearMap R s E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.domDomCongrLinearEquiv'_apply`：∀ (R : Type uR) (S : Type 
uS) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [inst : Semiring R]   [inst_
1 : (i : ι) → AddCommMonoid (M₁ i)…
· 使用定理 `MultilinearMap.domDomCongrLinearEquiv'_symm_apply`：∀ (R : Type uR) (S : 
Type uS) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [inst : Semiring R]   [
inst_1 : (i : ι) → AddCommMonoid (M₁ i)…
· 使用定理 `LinearEquiv.ofLinearMap.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M 
: Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] [ins…
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_reindex_symm (e : ι ≃ ι₂) (φ : MultilinearMap R s E) :
    lift φ ∘ₗ (reindex R s e).symm = lift (domDomCongrLinearEquiv' R R s _ e φ) := by
  ext; simp [reindex]
/-
**PiTensorProduct.lift_reindex** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：lift_reindex (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i => s (e.symm i)) E)
 (x : ⨂[R] i, s i) : lift φ (reindex R s e x) = lift ((domDomCongrLinearEquiv' R
 R s _ e).symm φ) x
参数：e : ι ≃ ι₂；φ : MultilinearMap R (fun i => s (e.symm i)) E；x : ⨂[R] i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `PiTensorProduct.lift_comp_reindex`：lift_comp_reindex (e : ι ≃ ι₂) (φ : M
ultilinearMap R (fun i => s (e.symm i)) E) : lift φ ∘ₗ (reindex R s e) = lift ((
domDomCongrLinearEquiv'…
-/
theorem lift_reindex
    (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i ↦ s (e.symm i)) E) (x : ⨂[R] i, s i) :
    lift φ (reindex R s e x) = lift ((domDomCongrLinearEquiv' R R s _ e).symm φ) x :=
  LinearMap.congr_fun (lift_comp_reindex e φ) x

@[simp]
/-
**PiTensorProduct.lift_reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：lift_reindex_symm (e : ι ≃ ι₂) (φ : MultilinearMap R s E) (x : ⨂[R] i, s (
e.symm i)) : lift φ (reindex R s e |>.symm x) = lift (domDomCongrLinearEquiv' R 
R s _ e φ) x
参数：e : ι ≃ ι₂；φ : MultilinearMap R s E；x : ⨂[R] i, s (e.symm i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `PiTensorProduct.lift_comp_reindex_symm`：lift_comp_reindex_symm (e : ι ≃ 
ι₂) (φ : MultilinearMap R s E) : lift φ ∘ₗ (reindex R s e).symm = lift (domDomCo
ngrLinearEquiv' R R s _ e φ)
-/
theorem lift_reindex_symm
    (e : ι ≃ ι₂) (φ : MultilinearMap R s E) (x : ⨂[R] i, s (e.symm i)) :
    lift φ (reindex R s e |>.symm x) = lift (domDomCongrLinearEquiv' R R s _ e φ) x :=
  LinearMap.congr_fun (lift_comp_reindex_symm e φ) x

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PiTensorProduct.reindex_trans** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) : (reindex R s e).trans (reindex
 R _ e') = reindex R s (e.trans e')
参数：e : ι ≃ ι₂；e' : ι₂ ≃ ι₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PiTensorProduct.reindex_tprod`：reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i)
 : reindex R s e (tprod R f) = tprod R fun i => f (e.symm i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PiTensorProduct.reindex_comp_tprod`：reindex_comp_tprod (e : ι ≃ ι₂) : (r
eindex R s e).compMultilinearMap (tprod R) = (domDomCongrLinearEquiv' R R s _ e)
.symm (tprod R)
-/
theorem reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) :
    (reindex R s e).trans (reindex R _ e') = reindex R s (e.trans e') := by
  apply LinearEquiv.toLinearMap_injective
  ext f
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_coe, reindex_tprod,
    LinearMap.coe_compMultilinearMap, Function.comp_apply,
    reindex_comp_tprod]
  congr
/-
**PiTensorProduct.reindex_reindex** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：reindex_reindex (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] i, s i) : reindex R 
_ e' (reindex R s e x) = reindex R s (e.trans e') x
参数：e : ι ≃ ι₂；e' : ι₂ ≃ ι₃；x : ⨂[R] i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.congr_fun`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `PiTensorProduct.reindex_trans`：reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃)
 : (reindex R s e).trans (reindex R _ e') = reindex R s (e.trans e')
-/
theorem reindex_reindex (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] i, s i) :
    reindex R _ e' (reindex R s e x) = reindex R s (e.trans e') x :=
  LinearEquiv.congr_fun (reindex_trans e e' : _ = reindex R s (e.trans e')) x

/-- This lemma is impractical to state in the dependent case. -/
@[simp]
/-
**PiTensorProduct.reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：reindex_symm (e : ι ≃ ι₂) : (reindex R (fun _ => M) e).symm = reindex R (f
un _ => M) e.symm
参数：e : ι ≃ ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.piCongrLeft'_symm`：∀ {α : Sort u_1} {β : Sort u_4} (P : Sort u_9) 
(e : α ≃ β),   (Equiv.piCongrLeft' (fun x => P) e).symm = Equiv.piCongrLeft' (fu
n a => P) e.s…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.domDomCongrLinearEquiv'_apply`：∀ (R : Type uR) (S : Type 
uS) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [inst : Semiring R]   [inst_
1 : (i : ι) → AddCommMonoid (M₁ i)…
· 使用定理 `MultilinearMap.mk.congr_simp`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → Ty
pe v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M
₁ i)] [inst_2 : Ad…
· 使用定理 `MultilinearMap.domDomCongrLinearEquiv'_symm_apply`：∀ (R : Type uR) (S : 
Type uS) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [inst : Semiring R]   [
inst_1 : (i : ι) → AddCommMonoid (M₁ i)…
· 使用定理 `LinearEquiv.ofLinearMap.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M 
: Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This lemma is impractical to state in the dependent case.
-/
theorem reindex_symm (e : ι ≃ ι₂) :
    (reindex R (fun _ ↦ M) e).symm = reindex R (fun _ ↦ M) e.symm := by
  ext x
  simp [reindex]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PiTensorProduct.reindex_refl** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：reindex_refl : reindex R s (Equiv.refl ι) = LinearEquiv.refl R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `MultilinearMap.mk.congr_simp`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → Ty
pe v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M
₁ i)] [inst_2 : Ad…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `PiTensorProduct.lift_tprod`：lift_tprod : lift (tprod R : MultilinearMap 
R s _) = LinearMap.id
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `LinearEquiv.ofLinearMap.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M 
: Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindex_refl : reindex R s (Equiv.refl ι) = LinearEquiv.refl R _ := by
  ext
  simp [reindex, domDomCongrLinearEquiv']

variable {t : ι → Type*}
variable [∀ i, AddCommMonoid (t i)] [∀ i, Module R (t i)]

/-- Re-indexing the components of the tensor product by an equivalence `e` is compatible
with `PiTensorProduct.map`. -/
/-
**PiTensorProduct.map_comp_reindex_eq** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct
`。
形式化陈述：map_comp_reindex_eq (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) : map (fun i =>
 f (e.symm i)) ∘ₗ reindex R s e = reindex R t e ∘ₗ map f
参数：f : Π i, s i ->ₗ[R] t i；e : ι ≃ ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.reindex_tprod`：reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i)
 : reindex R s e (tprod R f) = tprod R fun i => f (e.symm i)
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Re-indexing the components of the tensor product by an equivalence `e` is compat
ible
with `PiTensorProduct.map`.
-/
theorem map_comp_reindex_eq (f : Π i, s i →ₗ[R] t i) (e : ι ≃ ι₂) :
    map (fun i ↦ f (e.symm i)) ∘ₗ reindex R s e = reindex R t e ∘ₗ map f := by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearMap.comp_apply, reindex_tprod, map_tprod]
/-
**PiTensorProduct.map_reindex** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：map_reindex (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s i) : map
 (fun i => f (e.symm i)) (reindex R s e x) = reindex R t e (map f x)
参数：f : Π i, s i ->ₗ[R] t i；e : ι ≃ ι₂；x : ⨂[R] i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PiTensorProduct.map_comp_reindex_eq`：map_comp_reindex_eq (f : Π i, s i -
>ₗ[R] t i) (e : ι ≃ ι₂) : map (fun i => f (e.symm i)) ∘ₗ reindex R s e = reindex
 R t e ∘ₗ map f
-/
theorem map_reindex (f : Π i, s i →ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s i) :
    map (fun i ↦ f (e.symm i)) (reindex R s e x) = reindex R t e (map f x) :=
  DFunLike.congr_fun (map_comp_reindex_eq _ _) _
/-
**PiTensorProduct.map_comp_reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProdu
ct`。
形式化陈述：map_comp_reindex_symm (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) : map f ∘ₗ (r
eindex R s e).symm = (reindex R t e).symm ∘ₗ map (fun i => f (e.symm i))
参数：f : Π i, s i ->ₗ[R] t i；e : ι ≃ ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_reindex_symm (f : Π i, s i →ₗ[R] t i) (e : ι ≃ ι₂) :
    map f ∘ₗ (reindex R s e).symm = (reindex R t e).symm ∘ₗ map (fun i => f (e.symm i)) := by
  ext m
  apply LinearEquiv.injective (reindex R t e)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    comp_apply, ← map_reindex, LinearEquiv.apply_symm_apply, map_tprod]
/-
**PiTensorProduct.map_reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：map_reindex_symm (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s (e.
symm i)) : map f ((reindex R s e).symm x) = (reindex R t e).symm (map (fun i => 
f (e.symm i)) x)
参数：f : Π i, s i ->ₗ[R] t i；e : ι ≃ ι₂；x : ⨂[R] i, s (e.symm i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `PiTensorProduct.map_comp_reindex_symm`：map_comp_reindex_symm (f : Π i, s
 i ->ₗ[R] t i) (e : ι ≃ ι₂) : map f ∘ₗ (reindex R s e).symm = (reindex R t e).sy
mm ∘ₗ map (fun i => f (e.sy…
-/
theorem map_reindex_symm (f : Π i, s i →ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s (e.symm i)) :
    map f ((reindex R s e).symm x) = (reindex R t e).symm (map (fun i ↦ f (e.symm i)) x) :=
  DFunLike.congr_fun (map_comp_reindex_symm _ _) _

variable (ι)

attribute [local simp] eq_iff_true_of_subsingleton in
/-- The tensor product over an empty index type `ι` is isomorphic to the base ring. -/
@[simps symm_apply]
/-
**PiTensorProduct.isEmptyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：isEmptyEquiv [IsEmpty ι] : (⨂[R] i : ι, s i) ≃ₗ[R] R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product over an empty index type `ι` is isomorphic to the base ring.
-/
def isEmptyEquiv [IsEmpty ι] : (⨂[R] i : ι, s i) ≃ₗ[R] R where
  toFun := lift (constOfIsEmpty R _ 1)
  invFun r := r • tprod R (@isEmptyElim _ _ _)
  left_inv x := by
    refine x.induction_on ?_ ?_
    · intro x y
      simp only [map_smulₛₗ, RingHom.id_apply, lift.tprod, constOfIsEmpty_apply, const_apply,
        smul_eq_mul, mul_one]
      congr
      aesop
    · simp only
      intro x y hx hy
      rw [map_add, add_smul, hx, hy]
  right_inv t := by simp
  map_add' := map_add _
  map_smul' := map_smul _

@[simp]
/-
**PiTensorProduct.isEmptyEquiv_apply_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPr
oduct`。
形式化陈述：isEmptyEquiv_apply_tprod [IsEmpty ι] (f : Π i, s i) : isEmptyEquiv ι (tpro
d R f) = 1
参数：f : Π i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
-/
theorem isEmptyEquiv_apply_tprod [IsEmpty ι] (f : Π i, s i) :
    isEmptyEquiv ι (tprod R f) = 1 :=
  lift.tprod _

variable {ι}

section subsingleton

variable [Subsingleton ι] (i₀ : ι)

/-- Tensor product over a singleton type with element `i₀` is equivalent to `s i₀`. -/
/-
**PiTensorProduct.subsingletonEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：subsingletonEquiv : (⨂[R] i : ι, s i) ≃ₗ[R] s i₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product over a singleton type with element `i₀` is equivalent to `s i₀`.
-/
def subsingletonEquiv : (⨂[R] i : ι, s i) ≃ₗ[R] s i₀ :=
  LinearEquiv.ofLinearMap
    (lift
      { toFun f := f i₀
        map_update_add' m i := by rw [Subsingleton.elim i i₀]; simp
        map_update_smul' m i := by rw [Subsingleton.elim i i₀]; simp })
    ({ toFun x := tprod R (update (0 : (i : ι) → s i) i₀ x)
       map_add' := by simp
       map_smul' := by simp })
    (by ext _; simp)
    (by
      ext f
      have h : update (0 : (i : ι) → s i) i₀ (f i₀) = f := update_eq_self i₀ f
      simp [h])

@[simp]
/-
**PiTensorProduct.subsingletonEquiv_apply_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTen
sorProduct`。
形式化陈述：subsingletonEquiv_apply_tprod (f : (i : ι) -> s i) : subsingletonEquiv i₀ 
(⨂ₜ[R] i, f i) = f i₀
参数：f : (i : ι) -> s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
-/
theorem subsingletonEquiv_apply_tprod (f : (i : ι) → s i) :
    subsingletonEquiv i₀ (⨂ₜ[R] i, f i) = f i₀ := lift.tprod _
/-
**PiTensorProduct.subsingletonEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTens
orProduct`。
形式化陈述：subsingletonEquiv_symm_apply (x : s i₀) : (subsingletonEquiv i₀).symm x = 
tprod R (fun i => update (0 : (j : ι) -> s j) i₀ x i)
参数：x : s i₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subsingletonEquiv_symm_apply (x : s i₀) :
    (subsingletonEquiv i₀).symm x = tprod R (fun i ↦ update (0 : (j : ι) → s j) i₀ x i) := rfl

@[simp]
/-
**PiTensorProduct.subsingletonEquiv_symm_apply'** 是 Mathlib 中的一个引理，位于命名空间 `PiTen
sorProduct`。
形式化陈述：subsingletonEquiv_symm_apply' (x : M) : (subsingletonEquiv (s
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.subsingletonEquiv_apply_tprod`：subsingletonEquiv_apply_t
prod (f : (i : ι) -> s i) : subsingletonEquiv i₀ (⨂ₜ[R] i, f i) = f i₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subsingletonEquiv_symm_apply' (x : M) :
  (subsingletonEquiv (s := fun _ ↦ M) i₀).symm x = (tprod R fun _ ↦ x) := by
  simp [LinearEquiv.symm_apply_eq, subsingletonEquiv_apply_tprod]

end subsingleton

variable (R M)

section tmulEquivDep

variable (N : ι ⊕ ι₂ → Type*) [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type. If `N` is a constant family of
modules, use the non-dependent version `PiTensorProduct.tmulEquiv` instead. -/
/-
**PiTensorProduct.tmulEquivDep** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：tmulEquivDep : (⨂[R] i₁, N (.inl i₁)) otimes[R] (⨂[R] i₂, N (.inr i₂)) ≃ₗ[
R] ⨂[R] i, N i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type. If `N` is a constant family of
modules, use the non-dependent version `PiTensorProduct.tmulEquiv` instead.
-/
def tmulEquivDep :
    (⨂[R] i₁, N (.inl i₁)) ⊗[R] (⨂[R] i₂, N (.inr i₂)) ≃ₗ[R] ⨂[R] i, N i :=
  LinearEquiv.ofLinearMap
    (TensorProduct.lift
      { toFun a := PiTensorProduct.lift (PiTensorProduct.lift
          (MultilinearMap.currySumEquiv (tprod R)) a)
        map_add' := by simp
        map_smul' := by simp })
    (PiTensorProduct.lift (MultilinearMap.domCoprodDep (tprod R) (tprod R))) (by
      ext
      dsimp
      simp only [lift.tprod, domCoprodDep_apply, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
        currySum_apply]
      congr
      ext (_ | _) <;> simp)
    (TensorProduct.ext (by aesop))

@[simp]
/-
**PiTensorProduct.tmulEquivDep_apply** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`
。
形式化陈述：tmulEquivDep_apply (a : (i₁ : ι) -> N (.inl i₁)) (b : (i₂ : ι₂) -> N (.inr
 i₂)) : tmulEquivDep R N ((⨂ₜ[R] i₁, a i₁) otimesₜ (⨂ₜ[R] i₂, b i₂)) = (⨂ₜ[R] i,
 Sum.rec a b i)
参数：a : (i₁ : ι) -> N (.inl i₁)；b : (i₂ : ι₂) -> N (.inr i₂)。
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
· 使用定理 `MultilinearMap.currySumEquiv_apply`：∀ {R : Type uR} {ι : Type uι} {ι' : 
Type uι'} {M₂ : Type v₂} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₂]   [
inst_2 : _root_.Module R…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearEquiv.ofLinearMap.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M 
: Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] [ins…
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tmulEquivDep_apply (a : (i₁ : ι) → N (.inl i₁))
    (b : (i₂ : ι₂) → N (.inr i₂)) :
      tmulEquivDep R N ((⨂ₜ[R] i₁, a i₁) ⊗ₜ (⨂ₜ[R] i₂, b i₂)) =
        (⨂ₜ[R] i, Sum.rec a b i) := by
  simp [tmulEquivDep]

@[simp]
/-
**PiTensorProduct.tmulEquivDep_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorPro
duct`。
形式化陈述：tmulEquivDep_symm_apply (f : (i : ι oplus ι₂) -> N i) : (tmulEquivDep R N)
.symm (⨂ₜ[R] i, f i) = ((⨂ₜ[R] i₁, f (.inl i₁)) otimesₜ (⨂ₜ[R] i₂, f (.inr i₂)))
参数：f : (i : ι oplus ι₂) -> N i。
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
· 使用定理 `MultilinearMap.currySumEquiv_apply`：∀ {R : Type uR} {ι : Type uι} {ι' : 
Type uι'} {M₂ : Type v₂} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₂]   [
inst_2 : _root_.Module R…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearEquiv.ofLinearMap.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M 
: Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] [ins…
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.domCoprodDep_apply`：∀ {R : Type u_1} {ι₁ : Type u_2} {ι₂ 
: Type u_3} [inst : CommSemiring R] {N₁ : Type u_6} [inst_1 : AddCommMonoid N₁] 
  [inst_2 : _root_.Modu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tmulEquivDep_symm_apply (f : (i : ι ⊕ ι₂) → N i) :
    (tmulEquivDep R N).symm (⨂ₜ[R] i, f i) =
      ((⨂ₜ[R] i₁, f (.inl i₁)) ⊗ₜ (⨂ₜ[R] i₂, f (.inr i₂))) := by
  simp [tmulEquivDep]

end tmulEquivDep

section tmulEquiv

/-- Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type.

See `PiTensorProduct.tmulEquivDep` for the dependent version. -/
/-
**PiTensorProduct.tmulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：tmulEquiv : (⨂[R] (_ : ι), M) otimes[R] (⨂[R] (_ : ι₂), M) ≃ₗ[R] ⨂[R] (_ :
 ι oplus ι₂), M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type.

See `PiTensorProduct.tmulEquivDep` for the dependent version.
-/
def tmulEquiv :
    (⨂[R] (_ : ι), M) ⊗[R] (⨂[R] (_ : ι₂), M) ≃ₗ[R] ⨂[R] (_ : ι ⊕ ι₂), M :=
  tmulEquivDep R (fun _ ↦ M)

@[simp]
/-
**PiTensorProduct.tmulEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：tmulEquiv_apply (a : ι -> M) (b : ι₂ -> M) : tmulEquiv R M ((⨂ₜ[R] i, a i)
 otimesₜ[R] (⨂ₜ[R] i, b i)) = ⨂ₜ[R] i, Sum.elim a b i
参数：a : ι -> M；b : ι₂ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiTensorProduct.tmulEquivDep_apply`：tmulEquivDep_apply (a : (i₁ : ι) -> 
N (.inl i₁)) (b : (i₂ : ι₂) -> N (.inr i₂)) : tmulEquivDep R N ((⨂ₜ[R] i₁, a i₁)
 otimesₜ (⨂ₜ[R] i₂, b i₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tmulEquiv_apply (a : ι → M) (b : ι₂ → M) :
    tmulEquiv R M ((⨂ₜ[R] i, a i) ⊗ₜ[R] (⨂ₜ[R] i, b i)) = ⨂ₜ[R] i, Sum.elim a b i := by
  simp [tmulEquiv, Sum.elim]

@[simp]
/-
**PiTensorProduct.tmulEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduc
t`。
形式化陈述：tmulEquiv_symm_apply (a : ι oplus ι₂ -> M) : (tmulEquiv R M).symm (⨂ₜ[R] i
, a i) = (⨂ₜ[R] i, a (Sum.inl i)) otimesₜ[R] (⨂ₜ[R] i, a (Sum.inr i))
参数：a : ι oplus ι₂ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiTensorProduct.tmulEquivDep_symm_apply`：tmulEquivDep_symm_apply (f : (i
 : ι oplus ι₂) -> N i) : (tmulEquivDep R N).symm (⨂ₜ[R] i, f i) = ((⨂ₜ[R] i₁, f 
(.inl i₁)) otimesₜ (⨂ₜ[R] i₂,…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tmulEquiv_symm_apply (a : ι ⊕ ι₂ → M) :
    (tmulEquiv R M).symm (⨂ₜ[R] i, a i) =
      (⨂ₜ[R] i, a (Sum.inl i)) ⊗ₜ[R] (⨂ₜ[R] i, a (Sum.inr i)) := by
  simp [tmulEquiv]

end tmulEquiv

end Multilinear

end PiTensorProduct

end Semiring

section Ring

namespace PiTensorProduct

open PiTensorProduct

open TensorProduct

variable {ι : Type*} {R : Type*} [CommRing R]
variable {s : ι → Type*} [∀ i, AddCommGroup (s i)] [∀ i, Module R (s i)]

/-- Unlike for the binary tensor product, we require `R` to be a `CommRing` here, otherwise
this is false in the case where `ι` is empty. -/
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unlike for the binary tensor product, we require `R` to be a `CommRing` here, ot
herwise
this is false in the case where `ι` is empty.
-/
instance : AddCommGroup (⨂[R] i, s i) :=
  Module.addCommMonoidToAddCommGroup R

end PiTensorProduct

end Ring

