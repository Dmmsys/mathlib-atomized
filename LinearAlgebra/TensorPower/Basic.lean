/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# Tensor power of a semimodule over a commutative semiring

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `Fin n` of `M`,
`⨂[R] (i : Fin n), M`. This is a special case of `PiTensorProduct`.

This file introduces the notation `⨂[R]^n M` for `TensorPower R n M`, which in turn is an
abbreviation for `⨂[R] i : Fin n, M`.

## Main definitions:

* `TensorPower.gsemiring`: the tensor powers form a graded semiring.
* `TensorPower.galgebra`: the tensor powers form a graded algebra.

## Implementation notes

In this file we use `ₜ1` and `ₜ*` as local notation for the graded multiplicative structure on
tensor powers. Elsewhere, using `1` and `*` on `GradedMonoid` should be preferred.
-/

@[expose] public section

open scoped TensorProduct

/-- Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : Fin n), M`. -/
/-
**TensorPower** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TensorPower (R : Type*) (n : Nat) (M : Type*) [CommSemiring R] [AddCommMon
oid M] [Module R M] : Type _
参数：R : Type*；n : Nat；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : Fin n), M`.
-/
abbrev TensorPower (R : Type*) (n : ℕ) (M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] : Type _ :=
  ⨂[R] _ : Fin n, M

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

@[inherit_doc] scoped[TensorProduct] notation:max "⨂[" R "]^" n:arg => TensorPower R n

namespace PiTensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- Two dependent pairs of tensor products are equal if their index is equal and the contents
are equal after a canonical reindexing. -/
@[ext (iff := false)]
/-
**PiTensorProduct.gradedMonoid_eq_of_reindex_cast** 是 Mathlib 中的一个定理，位于命名空间 `PiT
ensorProduct`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {ιι : Type u_3} {ι : ιι → Type u_4} {a b
 : GradedMonoid fun ii => PiTensorProduct R fun x => M} (h : a.fst = b.fst),   (
PiTensorProduct.reindex R (fun x => M) (Equiv.cast ⋯)) a.snd = b.snd → a = b
参数：h : a.fst = b.fst；PiTensorProduct.reindex R (fun x => M) (Equiv.cast ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.reindex_refl`：reindex_refl : reindex R s (Equiv.refl ι) 
= LinearEquiv.refl R _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two dependent pairs of tensor products are equal if their index is equal and the
 contents
are equal after a canonical reindexing.
-/
theorem gradedMonoid_eq_of_reindex_cast {ιι : Type*} {ι : ιι → Type*} :
    ∀ {a b : GradedMonoid fun ii => ⨂[R] _ : ι ii, M} (h : a.fst = b.fst),
      reindex R (fun _ ↦ M) (Equiv.cast <| congr_arg ι h) a.snd = b.snd → a = b
  | ⟨ai, a⟩, ⟨bi, b⟩ => fun (hi : ai = bi) (h : reindex R (fun _ ↦ M) _ a = b) => by
    subst hi
    simp_all

end PiTensorProduct

namespace TensorPower

open scoped TensorProduct DirectSum

open PiTensorProduct

/-- As a graded monoid, `⨂[R]^i M` has a `1 : ⨂[R]^0 M`. -/
/-
**TensorPower.gOne** 是 Mathlib 中的一个实例，位于命名空间 `TensorPower`。
形式化陈述：gOne : GradedMonoid.GOne fun i => ⨂[R]^i M where one
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a graded monoid, `⨂[R]^i M` has a `1 : ⨂[R]^0 M`.
-/
instance gOne : GradedMonoid.GOne fun i => ⨂[R]^i M where one := tprod R <| @Fin.elim0 M

local notation "ₜ1" => @GradedMonoid.GOne.one ℕ (fun i => ⨂[R]^i M) _ _
/-
**TensorPower.gOne_def** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：gOne_def : ₜ1 = tprod R (@Fin.elim0 M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gOne_def : ₜ1 = tprod R (@Fin.elim0 M) :=
  rfl

/-- A variant of `PiTensorProduct.tmulEquiv` with the result indexed by `Fin (n + m)`. -/
/-
**TensorPower.mulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TensorPower`。
形式化陈述：mulEquiv {n m : Nat} : ⨂[R]^n M otimes[R] (⨂[R]^m) M ≃ₗ[R] (⨂[R]^(n + m)) 
M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `PiTensorProduct.tmulEquiv` with the result indexed by `Fin (n + m)
`.
-/
def mulEquiv {n m : ℕ} : ⨂[R]^n M ⊗[R] (⨂[R]^m) M ≃ₗ[R] (⨂[R]^(n + m)) M :=
  (tmulEquiv R M).trans (reindex R (fun _ ↦ M) finSumFinEquiv)

/-- As a graded monoid, `⨂[R]^i M` has a `(*) : ⨂[R]^i M → ⨂[R]^j M → ⨂[R]^(i + j) M`. -/
/-
**TensorPower.gMul** 是 Mathlib 中的一个实例，位于命名空间 `TensorPower`。
形式化陈述：gMul : GradedMonoid.GMul fun i => ⨂[R]^i M where mul {i j} a b
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a graded monoid, `⨂[R]^i M` has a `(*) : ⨂[R]^i M → ⨂[R]^j M → ⨂[R]^(i + j) M
`.
-/
instance gMul : GradedMonoid.GMul fun i => ⨂[R]^i M where
  mul {i j} a b :=
    (TensorProduct.mk R _ _).compr₂ (↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M)) a b

local infixl:70 " ₜ* " => @GradedMonoid.GMul.mul ℕ (fun i => ⨂[R]^i M) _ _ _ _
/-
**TensorPower.gMul_def** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：gMul_def {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) : a ₜ* b = @mulEquiv R M _ 
_ _ i j (a otimesₜ b)
参数：a : ⨂[R]^i M；b : (⨂[R]^j) M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gMul_def {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) :
    a ₜ* b = @mulEquiv R M _ _ _ i j (a ⊗ₜ b) :=
  rfl
/-
**TensorPower.gMul_eq_coe_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：gMul_eq_coe_linearMap {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) : a ₜ* b = ((T
ensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M) : ⨂[R]^i M 
->ₗ[R] (⨂[R]^j) M ->ₗ[R] (⨂[R]^(i + j)) M) a b
参数：a : ⨂[R]^i M；b : (⨂[R]^j) M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gMul_eq_coe_linearMap {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) :
    a ₜ* b = ((TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M) :
      ⨂[R]^i M →ₗ[R] (⨂[R]^j) M →ₗ[R] (⨂[R]^(i + j)) M) a b :=
  rfl

variable (R M)

/-- Cast between "equal" tensor powers. -/
/-
**TensorPower.cast** 是 Mathlib 中的一个定义，位于命名空间 `TensorPower`。
形式化陈述：cast {i j} (h : i = j) : ⨂[R]^i M ≃ₗ[R] (⨂[R]^j) M
参数：h : i = j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast between "equal" tensor powers.
-/
def cast {i j} (h : i = j) : ⨂[R]^i M ≃ₗ[R] (⨂[R]^j) M := reindex R (fun _ ↦ M) (finCongr h)
/-
**TensorPower.cast_tprod** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：cast_tprod {i j} (h : i = j) (a : Fin i -> M) : cast R M h (tprod R a) = t
prod R (a ∘ Fin.cast h.symm)
参数：h : i = j；a : Fin i -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.reindex_tprod`：reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i)
 : reindex R s e (tprod R f) = tprod R fun i => f (e.symm i)
-/
theorem cast_tprod {i j} (h : i = j) (a : Fin i → M) :
    cast R M h (tprod R a) = tprod R (a ∘ Fin.cast h.symm) :=
  reindex_tprod _ _

@[simp]
/-
**TensorPower.cast_refl** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：cast_refl {i} (h : i = i) : cast R M h = LinearEquiv.refl _ _
参数：h : i = i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `finCongr_refl`：∀ {n : ℕ} (h : optParam (n = n) ⋯), finCongr h = Equiv.re
fl (Fin n)
· 使用定理 `PiTensorProduct.reindex_refl`：reindex_refl : reindex R s (Equiv.refl ι) 
= LinearEquiv.refl R _
-/
theorem cast_refl {i} (h : i = i) : cast R M h = LinearEquiv.refl _ _ :=
  (congr_arg (reindex R fun _ ↦ M) <| finCongr_refl h).trans reindex_refl

@[simp]
/-
**TensorPower.cast_symm** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：cast_symm {i j} (h : i = j) : (cast R M h).symm = cast R M h.symm
参数：h : i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.reindex_symm`：reindex_symm (e : ι ≃ ι₂) : (reindex R (fu
n _ => M) e).symm = reindex R (fun _ => M) e.symm
-/
theorem cast_symm {i j} (h : i = j) : (cast R M h).symm = cast R M h.symm :=
  reindex_symm _

@[simp]
/-
**TensorPower.cast_trans** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：cast_trans {i j k} (h : i = j) (h' : j = k) : (cast R M h).trans (cast R M
 h') = cast R M (h.trans h')
参数：h : i = j；h' : j = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.reindex_trans`：reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃)
 : (reindex R s e).trans (reindex R _ e') = reindex R s (e.trans e')
-/
theorem cast_trans {i j k} (h : i = j) (h' : j = k) :
    (cast R M h).trans (cast R M h') = cast R M (h.trans h') :=
  reindex_trans _ _

variable {R M}

@[simp]
/-
**TensorPower.cast_cast** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：cast_cast {i j k} (h : i = j) (h' : j = k) (a : ⨂[R]^i M) : cast R M h' (c
ast R M h a) = cast R M (h.trans h') a
参数：h : i = j；h' : j = k；a : ⨂[R]^i M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.reindex_reindex`：reindex_reindex (e : ι ≃ ι₂) (e' : ι₂ ≃
 ι₃) (x : ⨂[R] i, s i) : reindex R _ e' (reindex R s e x) = reindex R s (e.trans
 e') x
-/
theorem cast_cast {i j k} (h : i = j) (h' : j = k) (a : ⨂[R]^i M) :
    cast R M h' (cast R M h a) = cast R M (h.trans h') a :=
  reindex_reindex _ _ _

@[ext (iff := false)]
/-
**TensorPower.gradedMonoid_eq_of_cast** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：gradedMonoid_eq_of_cast {a b : GradedMonoid fun n => ⨂[R] _ : Fin n, M} (h
 : a.fst = b.fst) (h2 : cast R M h a.snd = b.snd) : a = b
参数：h : a.fst = b.fst；h2 : cast R M h a.snd = b.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.gradedMonoid_eq_of_reindex_cast`：∀ {R : Type u_1} {M : T
ype u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Mod
ule R M]   {ιι : Type u_3} {ι : ιι → …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finCongr_eq_equivCast`：∀ {n m : ℕ} (h : n = m), finCongr h = Equiv.cast 
⋯
· 使用定理 `TensorPower.cast.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : CommSemir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {i j : ℕ} (h : 
i = j), Ten…
-/
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid fun n => ⨂[R] _ : Fin n, M} (h : a.fst = b.fst)
    (h2 : cast R M h a.snd = b.snd) : a = b := by
  refine gradedMonoid_eq_of_reindex_cast h ?_
  rw [cast] at h2
  rw [← finCongr_eq_equivCast, ← h2]
/-
**TensorPower.cast_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：cast_eq_cast {i j} (h : i = j) : ⇑(cast R M h) = _root_.cast (congrArg (fu
n i => ⨂[R]^i M) h)
参数：h : i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorPower.cast_refl`：cast_refl {i} (h : i = i) : cast R M h = LinearEq
uiv.refl _ _
-/
theorem cast_eq_cast {i j} (h : i = j) :
    ⇑(cast R M h) = _root_.cast (congrArg (fun i => ⨂[R]^i M) h) := by
  subst h
  rw [cast_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-
**TensorPower.tprod_mul_tprod** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：tprod_mul_tprod {na nb} (a : Fin na -> M) (b : Fin nb -> M) : tprod R a ₜ*
 tprod R b = tprod R (Fin.append a b)
参数：a : Fin na -> M；b : Fin nb -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.tmulEquiv_apply`：tmulEquiv_apply (a : ι -> M) (b : ι₂ ->
 M) : tmulEquiv R M ((⨂ₜ[R] i, a i) otimesₜ[R] (⨂ₜ[R] i, b i)) = ⨂ₜ[R] i, Sum.el
im a b i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PiTensorProduct.reindex_tprod`：reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i)
 : reindex R s e (tprod R f) = tprod R fun i => f (e.symm i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
-/
theorem tprod_mul_tprod {na nb} (a : Fin na → M) (b : Fin nb → M) :
    tprod R a ₜ* tprod R b = tprod R (Fin.append a b) := by
  dsimp [gMul_def, mulEquiv]
  rw [tmulEquiv_apply R M a b]
  refine (reindex_tprod _ _).trans ?_
  congr 1
  dsimp only [Fin.append, finSumFinEquiv, Equiv.coe_fn_symm_mk]
  apply funext
  apply Fin.addCases <;> simp
/-
**TensorPower.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：one_mul {n} (a : ⨂[R]^n M) : cast R M (zero_add n) (ₜ1 ₜ* a) = a
参数：a : ⨂[R]^n M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorPower.gMul_def`：gMul_def {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) : a
 ₜ* b = @mulEquiv R M _ _ _ i j (a otimesₜ b)
· 使用定理 `TensorPower.gOne_def`：gOne_def : ₜ1 = tprod R (@Fin.elim0 M)
· 使用定理 `PiTensorProduct.induction_on`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `PiTensorProduct.instIsScalarTower`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorPower.tprod_mul_tprod`：tprod_mul_tprod {na nb} (a : Fin na -> M) (
b : Fin nb -> M) : tprod R a ₜ* tprod R b = tprod R (Fin.append a b)
· 使用定理 `TensorPower.cast_tprod`：cast_tprod {i j} (h : i = j) (a : Fin i -> M) : 
cast R M h (tprod R a) = tprod R (a ∘ Fin.cast h.symm)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Fin.elim0_append`：elim0_append (v : Fin n -> α) : append Fin.elim0 v = v
 ∘ Fin.cast (Nat.zero_add _)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem one_mul {n} (a : ⨂[R]^n M) : cast R M (zero_add n) (ₜ1 ₜ* a) = a := by
  rw [gMul_def, gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [TensorProduct.tmul_smul, map_smul, map_smul, ← gMul_def, tprod_mul_tprod, cast_tprod]
    congr 2 with i
    rw [Fin.elim0_append]
    refine congr_arg a (Fin.ext ?_)
    simp
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
/-
**TensorPower.mul_one** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：mul_one {n} (a : ⨂[R]^n M) : cast R M (add_zero _) (a ₜ* ₜ1) = a
参数：a : ⨂[R]^n M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorPower.gMul_def`：gMul_def {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) : a
 ₜ* b = @mulEquiv R M _ _ _ i j (a otimesₜ b)
· 使用定理 `TensorPower.gOne_def`：gOne_def : ₜ1 = tprod R (@Fin.elim0 M)
· 使用定理 `PiTensorProduct.induction_on`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
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
· 使用定理 `TensorPower.tprod_mul_tprod`：tprod_mul_tprod {na nb} (a : Fin na -> M) (
b : Fin nb -> M) : tprod R a ₜ* tprod R b = tprod R (Fin.append a b)
· 使用定理 `TensorPower.cast_tprod`：cast_tprod {i j} (h : i = j) (a : Fin i -> M) : 
cast R M h (tprod R a) = tprod R (a ∘ Fin.cast h.symm)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.add_zero`：∀ (n : ℕ), n + 0 = n
· 使用定理 `Fin.append_elim0`：append_elim0 (u : Fin m -> α) : append u Fin.elim0 = u
 ∘ Fin.cast (Nat.add_zero _)
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem mul_one {n} (a : ⨂[R]^n M) : cast R M (add_zero _) (a ₜ* ₜ1) = a := by
  rw [gMul_def, gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [← TensorProduct.smul_tmul', map_smul, map_smul, ← gMul_def, tprod_mul_tprod R a _,
      cast_tprod]
    simp
  | add x y hx hy =>
    rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
/-
**TensorPower.mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：mul_assoc {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M)
 : cast R M (add_assoc _ _ _) (a ₜ* b ₜ* c) = a ₜ* (b ₜ* c)
参数：a : (⨂[R]^na) M；b : (⨂[R]^nb) M；c : (⨂[R]^nc) M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.instIsScalarTower`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorPower.tprod_mul_tprod`：tprod_mul_tprod {na nb} (a : Fin na -> M) (
b : Fin nb -> M) : tprod R a ₜ* tprod R b = tprod R (Fin.append a b)
· 使用定理 `TensorPower.cast_tprod`：cast_tprod {i j} (h : i = j) (a : Fin i -> M) : 
cast R M h (tprod R a) = tprod R (a ∘ Fin.cast h.symm)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Fin.append_assoc`：append_assoc {p : Nat} (a : Fin m -> α) (b : Fin n -> 
α) (c : Fin p -> α) : append (append a b) c = append a (append b c) ∘ Fin.cast (
Nat.ad…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Fin.val_cast`：∀ {n m : ℕ} (h : n = m) (i : Fin n), ↑(Fin.cast h i) = ↑i
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem mul_assoc {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M) :
    cast R M (add_assoc _ _ _) (a ₜ* b ₜ* c) = a ₜ* (b ₜ* c) := by
  let mul : ∀ n m : ℕ, ⨂[R]^n M →ₗ[R] (⨂[R]^m) M →ₗ[R] (⨂[R]^(n + m)) M := fun n m =>
    (TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(n + m)) M)
  -- replace `a`, `b`, `c` with `tprod R a`, `tprod R b`, `tprod R c`
  let e : (⨂[R]^(na + nb + nc)) M ≃ₗ[R] (⨂[R]^(na + (nb + nc))) M := cast R M (add_assoc _ _ _)
  let lhs : (⨂[R]^na) M →ₗ[R] (⨂[R]^nb) M →ₗ[R] (⨂[R]^nc) M →ₗ[R] (⨂[R]^(na + (nb + nc))) M :=
    (LinearMap.llcomp R _ _ _ ((mul _ nc).compr₂ e.toLinearMap)).comp (mul na nb)
  have lhs_eq : ∀ a b c, lhs a b c = e (a ₜ* b ₜ* c) := fun _ _ _ => rfl
  let rhs : (⨂[R]^na) M →ₗ[R] (⨂[R]^nb) M →ₗ[R] (⨂[R]^nc) M →ₗ[R] (⨂[R]^(na + (nb + nc))) M :=
    (LinearMap.llcomp R _ _ _ (LinearMap.lflip (R := R)).toLinearMap <|
        (LinearMap.llcomp R _ _ _ (mul na _).flip).comp (mul nb nc)).flip
  have rhs_eq : ∀ a b c, rhs a b c = a ₜ* (b ₜ* c) := fun _ _ _ => rfl
  suffices lhs = rhs from
    LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun this a) b) c
  ext a b c
  -- clean up
  simp only [e, LinearMap.compMultilinearMap_apply, lhs_eq, rhs_eq, tprod_mul_tprod, cast_tprod]
  congr 1 with j
  rw [Fin.append_assoc]
  refine congr_arg (Fin.append a (Fin.append b c)) (Fin.ext ?_)
  rw [Fin.val_cast, Fin.val_cast]

-- for now we just use the default for the `gnpow` field as it's easier.
/-
**TensorPower.gmonoid** 是 Mathlib 中的一个实例，位于命名空间 `TensorPower`。
形式化陈述：gmonoid : GradedMonoid.GMonoid fun i => ⨂[R]^i M
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance gmonoid : GradedMonoid.GMonoid fun i => ⨂[R]^i M :=
  { TensorPower.gMul, TensorPower.gOne with
    one_mul := fun _ => gradedMonoid_eq_of_cast (zero_add _) (one_mul _)
    mul_one := fun _ => gradedMonoid_eq_of_cast (add_zero _) (mul_one _)
    mul_assoc := fun _ _ _ => gradedMonoid_eq_of_cast (add_assoc _ _ _) (mul_assoc _ _ _) }

/-- The canonical map from `R` to `⨂[R]^0 M` corresponding to the `algebraMap` of the tensor
algebra. -/
/-
**TensorPower.algebraMap** 是 Mathlib 中的一个定义，位于命名空间 `TensorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `R` to `⨂[R]^0 M` corresponding to the `algebraMap` of th
e tensor
algebra.
-/
def algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M :=
  LinearEquiv.symm <| isEmptyEquiv (Fin 0)
/-
**TensorPower.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap₀_eq_smul_one (r : R) : (algebraMap₀ r : (⨂[R]^0) M) = r • ₜ1 := by
  simp [algebraMap₀]; congr
/-
**TensorPower.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap₀_one : (algebraMap₀ 1 : (⨂[R]^0) M) = ₜ1 :=
  (algebraMap₀_eq_smul_one 1).trans (one_smul _ _)
/-
**TensorPower.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap₀_mul {n} (r : R) (a : ⨂[R]^n M) :
    cast R M (zero_add _) (algebraMap₀ r ₜ* a) = r • a := by
  rw [gMul_eq_coe_linearMap, algebraMap₀_eq_smul_one, LinearMap.map_smul₂, map_smul,
    ← gMul_eq_coe_linearMap, one_mul]
/-
**TensorPower.mul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_algebraMap₀ {n} (r : R) (a : ⨂[R]^n M) :
    cast R M (add_zero _) (a ₜ* algebraMap₀ r) = r • a := by
  rw [gMul_eq_coe_linearMap, algebraMap₀_eq_smul_one, map_smul, map_smul, ← gMul_eq_coe_linearMap,
    mul_one]
/-
**TensorPower.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap₀_mul_algebraMap₀ (r s : R) :
    cast R M (add_zero _) (algebraMap₀ r ₜ* algebraMap₀ s) = algebraMap₀ (r * s) := by
  rw [← smul_eq_mul, map_smul]
  exact algebraMap₀_mul r (@algebraMap₀ R M _ _ _ s)
/-
**TensorPower.gsemiring** 是 Mathlib 中的一个实例，位于命名空间 `TensorPower`。
形式化陈述：gsemiring : DirectSum.GSemiring fun i => ⨂[R]^i M
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance gsemiring : DirectSum.GSemiring fun i => ⨂[R]^i M :=
  { TensorPower.gmonoid with
    mul_zero := fun _ => map_zero _
    zero_mul := fun _ => LinearMap.map_zero₂ _ _
    mul_add := fun _ _ _ => map_add _ _ _
    add_mul := fun _ _ _ => LinearMap.map_add₂ _ _ _ _
    natCast := fun n => algebraMap₀ (n : R)
    natCast_zero := by simp only [Nat.cast_zero, map_zero]
    natCast_succ := fun n => by simp only [Nat.cast_succ, map_add, algebraMap₀_one] }
/-
**TensorPower.** 是 Mathlib 中的一个示例，位于命名空间 `TensorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Semiring (⨁ n : ℕ, ⨂[R]^n M) := by infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The tensor powers form a graded algebra.

Note that this instance implies `Algebra R (⨁ n : ℕ, ⨂[R]^n M)` via `DirectSum.Algebra`. -/
/-
**TensorPower.galgebra** 是 Mathlib 中的一个实例，位于命名空间 `TensorPower`。
形式化陈述：galgebra : DirectSum.GAlgebra R fun i => ⨂[R]^i M where toFun
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorPower.algebraMap₀_one`：algebraMap₀_one : (algebraMap₀ 1 : (⨂[R]^0)
 M) = ₜ1

--- 原说明 ---
The tensor powers form a graded algebra.

Note that this instance implies `Algebra R (⨁ n : ℕ, ⨂[R]^n M)` via `DirectSum.A
lgebra`.
-/
instance galgebra : DirectSum.GAlgebra R fun i => ⨂[R]^i M where
  toFun := (algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M).toLinearMap.toAddMonoidHom
  map_one := algebraMap₀_one
  map_mul r s := gradedMonoid_eq_of_cast rfl (by
    rw [← LinearEquiv.eq_symm_apply]
    have := algebraMap₀_mul_algebraMap₀ (M := M) r s
    exact this.symm)
  commutes r x := gradedMonoid_eq_of_cast (add_comm _ _) (by
    have := (algebraMap₀_mul r x.snd).trans (mul_algebraMap₀ r x.snd).symm
    rw [← LinearEquiv.eq_symm_apply, cast_symm]
    rw [← LinearEquiv.eq_symm_apply, cast_symm, cast_cast] at this
    exact this)
  smul_def r x := gradedMonoid_eq_of_cast (zero_add x.fst).symm (by
    rw [← LinearEquiv.eq_symm_apply, cast_symm]
    exact (algebraMap₀_mul r x.snd).symm)
/-
**TensorPower.galgebra_toFun_def** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：galgebra_toFun_def (r : R) : DirectSum.GAlgebra.toFun (A
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem galgebra_toFun_def (r : R) :
    DirectSum.GAlgebra.toFun (A := fun i ↦ ⨂[R]^i M) r = algebraMap₀ r :=
  rfl
/-
**TensorPower.** 是 Mathlib 中的一个示例，位于命名空间 `TensorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Algebra R (⨁ n : ℕ, ⨂[R]^n M) := by infer_instance

end TensorPower

