/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Logic.Small.Basic

/-!
# Free modules

We introduce a class `Module.Free R M`, for `R` a `Semiring` and `M` an `R`-module and we provide
several basic instances for this class.

Use `Finsupp.linearCombination_id_surjective` to prove that any module is the quotient of a free
module.

## Main definition

* `Module.Free R M` : the class of free `R`-modules.
-/

@[expose] public section

assert_not_exists DirectSum Matrix TensorProduct

universe u v w z

variable {ι : Type*} (R : Type u) (M : Type v) (N : Type z)

namespace Module
section Basic

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- `Module.Free R M` is the statement that the `R`-module `M` is free. -/
/-
**Module.Free** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u) → (M : Type v) → [inst : Semiring R] → [inst_1 : AddCommMonoi
d M] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Module.Free R M` is the statement that the `R`-module `M` is free.
-/
class Free (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  exists_basis (R M) : Nonempty <| (I : Type v) × Basis I R M
/-
**Module.Free.exists_set** 是 Mathlib 中的一个定理，位于命名空间 `Module.Free`。
形式化陈述：∀ (R : Type u) (M : Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M]   [Module.Free R M], ∃ S, Nonempty (Module.Basis (
↑S) R M)
参数：R : Type u；M : Type v；Module.Basis (↑S) R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
-/
lemma Free.exists_set [Free R M] : ∃ S : Set M, Nonempty (Basis S R M) :=
  let ⟨_I, b⟩ := exists_basis R M; ⟨Set.range b, ⟨b.reindexRange⟩⟩
/-
**Module.free_iff_set** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：free_iff_set : Free R M ↔ exists S : Set M, Nonempty (Basis S R M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_set`：∀ (R : Type u) (M : Type v) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Free R M], ∃ S
, Nonempty (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_sigma`：nonempty_sigma : Nonempty (Σ a : α, γ a) ↔ exists a : α,
 Nonempty (γ a)
-/
theorem free_iff_set : Free R M ↔ ∃ S : Set M, Nonempty (Basis S R M) :=
  ⟨fun _ ↦ Free.exists_set .., fun ⟨S, hS⟩ ↦ ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩

/-- If `M` fits in universe `w`, then freeness is equivalent to existence of a basis in that
universe.

Note that if `M` does not fit in `w`, the reverse direction of this implication is still true as
`Module.Free.of_basis`. -/
/-
**Module.free_def** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：free_def [Small.{w, v} M] : Free R M ↔ exists I : Type w, Nonempty (Basis 
I R M) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_sigma`：nonempty_sigma : Nonempty (Σ a : α, γ a) ↔ exists a : α,
 Nonempty (γ a)

--- 原说明 ---
If `M` fits in universe `w`, then freeness is equivalent to existence of a basis
 in that
universe.

Note that if `M` does not fit in `w`, the reverse direction of this implication 
is still true as
`Module.Free.of_basis`.
-/
theorem free_def [Small.{w, v} M] : Free R M ↔ ∃ I : Type w, Nonempty (Basis I R M) where
  mp h :=
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩
  mpr h := ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩

variable {R M}
/-
**Module.Free.of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Free`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module.Basis ι R M), Module.Fr
ee R M
参数：b : Module.Basis ι R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.free_def`：free_def [Small.{w, v} M] : Free R M ↔ exists I : Type 
w, Nonempty (Basis I R M) where mp h
-/
theorem Free.of_basis {ι : Type w} (b : Basis ι R M) : Free R M :=
  (free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩

end Basic

namespace Free

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
variable [AddCommMonoid N] [Module R N]

/-- If `Module.Free R M` then `ChooseBasisIndex R M` is the `ι` which indexes the basis
  `ι → M`. Note that this is defined such that this type is finite if `R` is trivial. -/
/-
**Module.Free.ChooseBasisIndex** 是 Mathlib 中的一个定义，位于命名空间 `Module.Free`。
形式化陈述：ChooseBasisIndex : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Module.Free R M` then `ChooseBasisIndex R M` is the `ι` which indexes the ba
sis
  `ι → M`. Note that this is defined such that this type is finite if `R` is tri
vial.
-/
def ChooseBasisIndex : Type _ :=
  ((Module.free_iff_set R M).mp ‹_›).choose

/-- There is no hope of computing this, but we add the instance anyway to avoid fumbling with
`open scoped Classical`. -/
/-
**Module.Free.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is no hope of computing this, but we add the instance anyway to avoid fumb
ling with
`open scoped Classical`.
-/
noncomputable instance : DecidableEq (ChooseBasisIndex R M) := Classical.decEq _

/-- If `Module.Free R M` then `chooseBasis : ι → M` is the basis.
Here `ι = ChooseBasisIndex R M`. -/
/-
**Module.Free.chooseBasis** 是 Mathlib 中的一个定义，位于命名空间 `Module.Free`。
形式化陈述：chooseBasis : Basis (ChooseBasisIndex R M) R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Module.Free R M` then `chooseBasis : ι → M` is the basis.
Here `ι = ChooseBasisIndex R M`.
-/
noncomputable def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  ((Module.free_iff_set R M).mp ‹_›).choose_spec.some

/-- The universal property of free modules: giving a function `(ChooseBasisIndex R M) → N`, for `N`
an `R`-module, is the same as giving an `R`-linear map `M →ₗ[R] N`.

This definition is parameterized over an extra `Semiring S`,
such that `SMulCommClass R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `AddEquiv` by setting `S := ℕ`.
See library note [bundled maps over different rings]. -/
/-
**Module.Free.constr** 是 Mathlib 中的一个定义，位于命名空间 `Module.Free`。
形式化陈述：constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] : (Cho
oseBasisIndex R M -> N) ≃ₗ[S] M ->ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of free modules: giving a function `(ChooseBasisIndex R M
) → N`, for `N`
an `R`-module, is the same as giving an `R`-linear map `M →ₗ[R] N`.

This definition is parameterized over an extra `Semiring S`,
such that `SMulCommClass R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `AddEquiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
noncomputable def constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] :
    (ChooseBasisIndex R M → N) ≃ₗ[S] M →ₗ[R] N :=
  Basis.constr (chooseBasis R M) S
/-
**Module.Free.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instIsTorsionFree : IsTorsionFree R M :=
  let ⟨⟨_, b⟩⟩ := exists_basis (R := R) (M := M)
  b.isTorsionFree
/-
**Module.Free.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : Nonempty (Module.Free.ChooseBasisIndex R M) :=
  (Module.Free.chooseBasis R M).index_nonempty
/-
**Module.Free.infinite** 是 Mathlib 中的一个定理，位于命名空间 `Module.Free`。
形式化陈述：infinite [Infinite R] [Nontrivial M] : Infinite M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.infinite_iff`：Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infini
te β
· 使用定理 `Module.Free.instNonemptyChooseBasisIndexOfNontrivial`：∀ (R : Type u) (M 
: Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   [inst_3 : Module.Free R M] [Nontri…
-/
theorem infinite [Infinite R] [Nontrivial M] : Infinite M :=
  (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right
/-
**Module.Free.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : FaithfulSMul R M :=
  .of_injective _ (chooseBasis R M).repr.symm.injective

variable {R M N}
/-
**Module.Free.of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Module.Free`。
形式化陈述：of_equiv {R R' M M' : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [
Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->+* R'} {σ' : R' ->+* R} 
[RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (e₂ : M ≃ₛₗ[σ] M') [Module.Free R M]
 : Module.Free R' M'
参数：e₂ : M ≃ₛₗ[σ] M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `Finsupp.mapRange.addEquiv_apply`：∀ {ι : Type u_1} {M : Type u_3} {N : Ty
pe u_4} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] (em' : M ≃+ N)   (g 
: ι →₀ M), (Finsupp.m…
· 使用定理 `RingHomInvPair.toRingEquiv_apply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] (σ : R₁ →+* R₂) (σ' : R₂ →+* R₁)   [inst
_2 : RingHomInvPair σ …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
lemma of_equiv {R R' M M' : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] M') [Module.Free R M] :
    Module.Free R' M' := by
  let e₁ : R ≃+* R' := RingHomInvPair.toRingEquiv σ σ'
  let I := Module.Free.ChooseBasisIndex R M
  obtain ⟨e₃ : M ≃ₗ[R] I →₀ R⟩ := Module.Free.chooseBasis R M
  let e : M' ≃+ (I →₀ R') :=
    (e₂.symm.trans e₃).toAddEquiv.trans (Finsupp.mapRange.addEquiv (ι := I) e₁.toAddEquiv)
  have he (x) : e x = Finsupp.mapRange.addEquiv (ι := I) e₁.toAddEquiv (e₃ (e₂.symm x)) := rfl
  let e' : M' ≃ₗ[R'] (I →₀ R') :=
    { __ := e, map_smul' := fun m x ↦ Finsupp.ext fun i ↦ by simp [e₁, he, map_smulₛₗ] }
  exact of_basis (.ofRepr e')

/-- A variation of `of_equiv`: the assumption `Module.Free R P` here is explicit rather than an
instance. -/
/-
**Module.Free.of_equiv'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Free`。
形式化陈述：of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.Free R P
) (e : P ≃ₗ[R] N) : Module.Free R N
参数：_ : Module.Free R P；e : P ≃ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…

--- 原说明 ---
A variation of `of_equiv`: the assumption `Module.Free R P` here is explicit rat
her than an
instance.
-/
theorem of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.Free R P)
    (e : P ≃ₗ[R] N) : Module.Free R N :=
  of_equiv e
/-
**Module.Free.iff_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Module.Free`。
形式化陈述：iff_of_equiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M] [Semi
ring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->+* R'} {σ' : R' ->+* R} [Rin
gHomInvPair σ σ'] [RingHomInvPair σ' σ] (e₂ : M ≃ₛₗ[σ] M') : Module.Free R M ↔ M
odule.Free R' M'
参数：e₂ : M ≃ₛₗ[σ] M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
-/
lemma iff_of_equiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] M') :
    Module.Free R M ↔ Module.Free R' M' :=
  ⟨fun _ ↦ of_equiv e₂, fun _ ↦ of_equiv e₂.symm⟩

@[deprecated (since := "2026-02-14")] alias of_ringEquiv := of_equiv
@[deprecated (since := "2026-02-14")] alias iff_of_ringEquiv := iff_of_equiv
/-
**Module.Free.shrink** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
形式化陈述：shrink [Small.{w} M] : Module.Free R (Shrink.{w} M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
-/
instance shrink [Small.{w} M] : Module.Free R (Shrink.{w} M) :=
  Module.Free.of_equiv (Shrink.linearEquiv R M).symm

set_option linter.dupNamespace false in
@[deprecated (since := "2026-04-18")] alias Module.free_shrink := shrink

variable (R M N)

/-- The module structure provided by `Semiring.toModule` is free. -/
/-
**Module.Free.self** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
形式化陈述：self : Module.Free R R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…

--- 原说明 ---
The module structure provided by `Semiring.toModule` is free.
-/
instance self : Module.Free R R :=
  of_basis (Basis.singleton Unit R)
/-
**Module.Free.ulift** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
形式化陈述：ulift : Free R (ULift M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
-/
instance ulift : Free R (ULift M) := of_equiv ULift.moduleEquiv.symm
/-
**Module.Free.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_subsingleton [Subsingleton N] : Module.Free R N :=
  of_basis.{u, z, z} (Basis.empty N : Basis PEmpty R N)

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
/-
**Module.Free.of_subsingleton'** 是 Mathlib 中的一个引理，位于命名空间 `Module.Free`。
形式化陈述：of_subsingleton' [Subsingleton R] : Module.Free R N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_subsingleton`：∀ (R : Type u) (N : Type z) [inst : Semirin
g R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R N]   [Subsingleton N],
 Module.Free R N
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
-/
lemma of_subsingleton' [Subsingleton R] : Module.Free R N :=
  letI := Module.subsingleton R N
  Module.Free.of_subsingleton R N

end Semiring

end Free

namespace Basis

open Finset

variable {S : Type*} [CommRing R] [Ring S] [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
variable {R} in
/-- If `B` is a basis of the `R`-algebra `S` such that `B i = 1` for some index `i`, then
each `r : R` gets represented as `s • B i` as an element of `S`. -/
/-
**Module.Basis.repr_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_algebraMap {ι : Type*} {B : Basis ι R S} {i : ι} (hBi : B i = 1) (r :
 R) : B.repr (algebraMap R S r) = Finsupp.single i r
参数：hBi : B i = 1；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `B` is a basis of the `R`-algebra `S` such that `B i = 1` for some index `i`,
 then
each `r : R` gets represented as `s • B i` as an element of `S`.
-/
theorem repr_algebraMap {ι : Type*} {B : Basis ι R S} {i : ι} (hBi : B i = 1) (r : R) :
    B.repr (algebraMap R S r) = Finsupp.single i r := by
  ext j; simp [Algebra.algebraMap_eq_smul_one, ← hBi]

end Basis

namespace End
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Free R M]

/-
**Module.End.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：mem_center_iff {f : End R M} : f in Set.center (End R M) ↔ exists (α : R) 
(hα : α in Set.center R), f = smulLeft α hα
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `Module.Basis.index_nonempty`：index_nonempty (b : Basis ι R M) [Nontrivia
l M] : Nonempty ι
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Module.End.smulLeft_apply`：∀ {R : Type u_1} {M : Type u_4} [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (α : R)   (hα : α
 ∈ Set.center R…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
theorem mem_center_iff {f : End R M} :
    f ∈ Set.center (End R M) ↔ ∃ (α : R) (hα : α ∈ Set.center R), f = smulLeft α hα := by
  simp only [Semigroup.mem_center_iff, LinearMap.ext_iff, mul_apply]
  refine ⟨fun h ↦ ?_, by simp_all⟩
  by_cases! Subsingleton M
  · exact ⟨0, by simp, fun _ ↦ Subsingleton.allEq _ _⟩
  let b := Free.chooseBasis R M
  let i := b.index_nonempty.some
  have H x : f x = b.repr (f (b i)) i • x := by simpa using (h ((b.coord i).smulRight x) (b i)).symm
  exact ⟨b.coord i <| f <| b i, fun r ↦ by simpa using congr(b.coord i $(H <| r • b i)), H⟩
/-
**Module.End.mem_submonoidCenter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：mem_submonoidCenter_iff {f : End R M} : f in Submonoid.center (End R M) ↔ 
exists (α : R) (hα : α in Submonoid.center R), f = smulLeft α hα
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.mem_center_iff`：mem_center_iff {f : End R M} : f in Set.cente
r (End R M) ↔ exists (α : R) (hα : α in Set.center R), f = smulLeft α hα
-/
theorem mem_submonoidCenter_iff {f : End R M} :
    f ∈ Submonoid.center (End R M) ↔ ∃ (α : R) (hα : α ∈ Submonoid.center R), f = smulLeft α hα :=
  mem_center_iff
/-
**Module.End.mem_subsemigroupCenter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：mem_subsemigroupCenter_iff {f : End R M} : f in Subsemigroup.center (End R
 M) ↔ exists (α : R) (hα : α in Subsemigroup.center R), f = smulLeft α hα
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.mem_center_iff`：mem_center_iff {f : End R M} : f in Set.cente
r (End R M) ↔ exists (α : R) (hα : α in Set.center R), f = smulLeft α hα
-/
theorem mem_subsemigroupCenter_iff {f : End R M} :
    f ∈ Subsemigroup.center (End R M) ↔
      ∃ (α : R) (hα : α ∈ Subsemigroup.center R), f = smulLeft α hα :=
  mem_center_iff

end Module.End

