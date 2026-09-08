/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Lemmas about the `IsSMulRegular` Predicate

For modules over a ring the proposition `IsSMulRegular r M` is equivalent to
`r` being a *non-zero-divisor*, i.e. `r • x = 0` only if `x = 0` for `x ∈ M`.
This specific result is `isSMulRegular_iff_smul_eq_zero_imp_eq_zero`.
Lots of results starting from this, especially ones about quotients (which
don't make sense without some algebraic assumptions), are in this file.
We don't pollute the `Mathlib/Algebra/Regular/SMul.lean` file with these because
it's supposed to import a minimal amount of the algebraic hierarchy.

## Tags

module, regular element, commutative algebra
-/

public section

section Congr

variable {R S M N} [Semiring R] [Semiring S] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [AddCommMonoid M] [Module R M]

/-
**LinearEquiv.isSMulRegular_congr'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.isSMulRegular_congr' [AddCommMonoid N] [Module S N] (e : M ≃ₛₗ
[σ] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N (σ r)
参数：e : M ≃ₛₗ[σ] N；r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.isSMulRegular_congr`：Equiv.isSMulRegular_congr {R S M M'} [SMul R 
M] [SMul S M'] {e : M ≃ M'} {r : R} {s : S} (h : forall x, e (r • x) = s • e x) 
: IsSMulRegular…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
-/
lemma LinearEquiv.isSMulRegular_congr' [AddCommMonoid N] [Module S N]
    (e : M ≃ₛₗ[σ] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N (σ r) :=
  e.toEquiv.isSMulRegular_congr (e.map_smul' r)
/-
**LinearEquiv.isSMulRegular_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.isSMulRegular_congr [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R
] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N r
参数：e : M ≃ₗ[R] N；r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearEquiv.isSMulRegular_congr'`：LinearEquiv.isSMulRegular_congr' [AddC
ommMonoid N] [Module S N] (e : M ≃ₛₗ[σ] N) (r : R) : IsSMulRegular M r ↔ IsSMulR
egular N (σ r)
-/
lemma LinearEquiv.isSMulRegular_congr [AddCommMonoid N] [Module R N]
    (e : M ≃ₗ[R] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N r :=
  e.isSMulRegular_congr' r

end Congr

variable {R S M M' M'' : Type*}

/-
**IsSMulRegular.submodule** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSMulRegular.submodule [Semiring R] [AddCommMonoid M] [Module R M] (N : S
ubmodule R M) (r : R) (h : IsSMulRegular M r) : IsSMulRegular N r
参数：N : Submodule R M；r : R；h : IsSMulRegular M r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSMulRegular.of_injective`：IsSMulRegular.of_injective {R M : Type*} [SM
ul R M] {N F} [SMul R N] [FunLike F M N] [MulActionHomClass F R M N] (f : F) {r 
: R} (h1 : Funct…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
-/
lemma IsSMulRegular.submodule [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (r : R) (h : IsSMulRegular M r) : IsSMulRegular N r :=
  h.of_injective N.subtype N.injective_subtype

section TensorProduct

open scoped TensorProduct

variable (M) [CommRing R] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] [Module.Flat R M] {r : R}
    (h : IsSMulRegular M' r)
include h

/-
**IsSMulRegular.lTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSMulRegular.lTensor : IsSMulRegular (M otimes[R] M') r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.lTensor_smul_action`：lTensor_smul_action (r : R) : (DistribSMu
l.toLinearMap R N r).lTensor M = DistribSMul.toLinearMap R (M otimes[R] N) r
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
-/
lemma IsSMulRegular.lTensor : IsSMulRegular (M ⊗[R] M') r :=
  have h1 := congrArg DFunLike.coe (LinearMap.lTensor_smul_action M M' r)
  h1.subst (Module.Flat.lTensor_preserves_injective_linearMap _ h)
/-
**IsSMulRegular.rTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSMulRegular.rTensor : IsSMulRegular (M' otimes[R] M) r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_smul_action`：rTensor_smul_action (r : R) : (DistribSMu
l.toLinearMap R N r).rTensor M = DistribSMul.toLinearMap R (N otimes[R] M) r
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
-/
lemma IsSMulRegular.rTensor : IsSMulRegular (M' ⊗[R] M) r :=
  have h1 := congrArg DFunLike.coe (LinearMap.rTensor_smul_action M M' r)
  h1.subst (Module.Flat.rTensor_preserves_injective_linearMap _ h)

end TensorProduct

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    (N : Submodule R M) (r : R)

/-
**isSMulRegular_submodule_iff_right_eq_zero_of_smul** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：isSMulRegular_submodule_iff_right_eq_zero_of_smul : IsSMulRegular N r ↔ fo
rall x in N, r • x = 0 -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `isSMulRegular_iff_right_eq_zero_of_smul`：isSMulRegular_iff_right_eq_zero
_of_smul [AddGroup M] [DistribSMul R M] {r : R} : IsSMulRegular M r ↔ forall m :
 M, r • m = 0 -> m = 0 where …
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSMulRegular_submodule_iff_right_eq_zero_of_smul :
    IsSMulRegular N r ↔ ∀ x ∈ N, r • x = 0 → x = 0 :=
  isSMulRegular_iff_right_eq_zero_of_smul.trans <|
    Subtype.forall.trans <| by
      simp only [SetLike.mk_smul_mk, Submodule.mk_eq_zero]
/-
**isSMulRegular_quotient_iff_mem_of_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_quotient_iff_mem_of_smul_mem : IsSMulRegular (M ⧸ N) r ↔ for
all x : M, r • x in N -> x in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `isSMulRegular_iff_right_eq_zero_of_smul`：isSMulRegular_iff_right_eq_zero
_of_smul [AddGroup M] [DistribSMul R M] {r : R} : IsSMulRegular M r ↔ forall m :
 M, r • m = 0 -> m = 0 where …
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSMulRegular_quotient_iff_mem_of_smul_mem :
    IsSMulRegular (M ⧸ N) r ↔ ∀ x : M, r • x ∈ N → x ∈ N :=
  isSMulRegular_iff_right_eq_zero_of_smul.trans <|
    N.mkQ_surjective.forall.trans <| by
      simp_rw [← map_smul, N.mkQ_apply, Submodule.Quotient.mk_eq_zero]

variable {N r}
/-
**mem_of_isSMulRegular_quotient_of_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_of_isSMulRegular_quotient_of_smul_mem (h1 : IsSMulRegular (M ⧸ N) r) {
x : M} (h2 : r • x in N) : x in N
参数：h1 : IsSMulRegular (M ⧸ N) r；h2 : r • x in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isSMulRegular_quotient_iff_mem_of_smul_mem`：isSMulRegular_quotient_iff_m
em_of_smul_mem : IsSMulRegular (M ⧸ N) r ↔ forall x : M, r • x in N -> x in N
-/
lemma mem_of_isSMulRegular_quotient_of_smul_mem (h1 : IsSMulRegular (M ⧸ N) r)
    {x : M} (h2 : r • x ∈ N) : x ∈ N :=
  (isSMulRegular_quotient_iff_mem_of_smul_mem N r).mp h1 x h2

/-- Given a left exact sequence `0 → M → M' → M''`, if `r` is regular on both
`M` and `M''` it's regular `M'` too. -/
/-
**isSMulRegular_of_range_eq_ker** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_of_range_eq_ker {f : M ->ₗ[R] M'} {g : M' ->ₗ[R] M''} (hf : 
Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g) (h1 : IsSMulRe
gular M r) (h2 : IsSMulRegular M'' r) : IsSMulRegular M' r
参数：hf : Function.Injective f；hfg : LinearMap.range f = LinearMap.ker g；h1 : IsSM
ulRegular M r；h2 : IsSMulRegular M'' r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_right_eq_zero_of_smul`：∀ {R : Type u_1} {M : Type u_3} 
[inst : AddGroup M] [inst_1 : DistribSMul R M] {r : R},   (∀ (m : M), r • m = 0 
→ m = 0) → IsSMulRegular M r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSMulRegular.right_eq_zero_of_smul`：∀ {R : Type u_1} {M : Type u_3} [in
st : Zero M] [inst_1 : SMulZeroClass R M] {r : R} {x : M},   IsSMulRegular M r →
 r • x = 0 → x = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…

--- 原说明 ---
Given a left exact sequence `0 → M → M' → M''`, if `r` is regular on both
`M` and `M''` it's regular `M'` too.
-/
lemma isSMulRegular_of_range_eq_ker {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (h1 : IsSMulRegular M r) (h2 : IsSMulRegular M'' r) :
    IsSMulRegular M' r := by
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro x hx
  obtain ⟨y, ⟨⟩⟩ := (congrArg (x ∈ ·) hfg).mpr <| h2.right_eq_zero_of_smul <|
    (g.map_smul r x).symm.trans <| (congrArg _ hx).trans g.map_zero
  refine (congrArg f (h1.right_eq_zero_of_smul ?_)).trans f.map_zero
  exact hf <| (f.map_smul r y).trans <| hx.trans f.map_zero.symm
/-
**isSMulRegular_of_isSMulRegular_on_submodule_on_quotient** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：isSMulRegular_of_isSMulRegular_on_submodule_on_quotient (h1 : IsSMulRegula
r N r) (h2 : IsSMulRegular (M ⧸ N) r) : IsSMulRegular M r
参数：h1 : IsSMulRegular N r；h2 : IsSMulRegular (M ⧸ N) r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isSMulRegular_of_range_eq_ker`：isSMulRegular_of_range_eq_ker {f : M ->ₗ[
R] M'} {g : M' ->ₗ[R] M''} (hf : Function.Injective f) (hfg : LinearMap.range f 
= LinearMap.ker g) …
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
-/
lemma isSMulRegular_of_isSMulRegular_on_submodule_on_quotient
    (h1 : IsSMulRegular N r) (h2 : IsSMulRegular (M ⧸ N) r) : IsSMulRegular M r :=
  isSMulRegular_of_range_eq_ker N.injective_subtype
    (N.range_subtype.trans N.ker_mkQ.symm) h1 h2

end Ring

section CommRing

open Submodule Pointwise

variable (M) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    (N : Submodule R M) (r : R)

variable (R) in
/-
**biUnion_associatedPrimes_eq_compl_regular** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biUnion_associatedPrimes_eq_compl_regular [IsNoetherianRing R] : ⋃ p in as
sociatedPrimes R M, p = { r : R | IsSMulRegular M r }ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `biUnion_associatedPrimes_eq_zero_divisors`：biUnion_associatedPrimes_eq_z
ero_divisors [IsNoetherianRing R] : ⋃ p in associatedPrimes R M, p = { r : R | e
xists x : M, x != 0 ∧ r • x = 0…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biUnion_associatedPrimes_eq_compl_regular [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R M, p = { r : R | IsSMulRegular M r }ᶜ :=
  Eq.trans (biUnion_associatedPrimes_eq_zero_divisors R M) <| by
    simp_rw [Set.compl_ofPred, isSMulRegular_iff_right_eq_zero_of_smul,
      not_forall, exists_prop, and_comm]
/-
**isSMulRegular_iff_ker_lsmul_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_iff_ker_lsmul_eq_bot : IsSMulRegular M r ↔ LinearMap.ker (Li
nearMap.lsmul R M r) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isSMulRegular_iff_torsionBy_eq_bot`：isSMulRegular_iff_torsionBy_eq_bot {
R} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (r : R) : IsSMulRegula
r M r ↔ Submodule.torsio…
-/
lemma isSMulRegular_iff_ker_lsmul_eq_bot :
    IsSMulRegular M r ↔ LinearMap.ker (LinearMap.lsmul R M r) = ⊥ :=
  isSMulRegular_iff_torsionBy_eq_bot M r

variable {M}
/-
**isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule : IsSMulRegula
r N r ↔ Disjoint (LinearMap.ker (LinearMap.lsmul R M r)) N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `isSMulRegular_submodule_iff_right_eq_zero_of_smul`：isSMulRegular_submodu
le_iff_right_eq_zero_of_smul : IsSMulRegular N r ↔ forall x in N, r • x = 0 -> x
 = 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
-/
lemma isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule :
    IsSMulRegular N r ↔ Disjoint (LinearMap.ker (LinearMap.lsmul R M r)) N :=
  Iff.trans (isSMulRegular_submodule_iff_right_eq_zero_of_smul N r) <|
    Iff.symm <| Iff.trans disjoint_comm disjoint_def
/-
**isSMulRegular_on_quot_iff_lsmul_comap_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_on_quot_iff_lsmul_comap_le : IsSMulRegular (M ⧸ N) r ↔ N.com
ap (LinearMap.lsmul R M r) <= N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isSMulRegular_quotient_iff_mem_of_smul_mem`：isSMulRegular_quotient_iff_m
em_of_smul_mem : IsSMulRegular (M ⧸ N) r ↔ forall x : M, r • x in N -> x in N
-/
lemma isSMulRegular_on_quot_iff_lsmul_comap_le :
    IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) ≤ N :=
  isSMulRegular_quotient_iff_mem_of_smul_mem N r
/-
**isSMulRegular_on_quot_iff_lsmul_comap_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_on_quot_iff_lsmul_comap_eq : IsSMulRegular (M ⧸ N) r ↔ N.com
ap (LinearMap.lsmul R M r) = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `isSMulRegular_on_quot_iff_lsmul_comap_le`：isSMulRegular_on_quot_iff_lsmu
l_comap_le : IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) <= N
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
lemma isSMulRegular_on_quot_iff_lsmul_comap_eq :
    IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) = N :=
  Iff.trans (isSMulRegular_on_quot_iff_lsmul_comap_le N r) <|
    LE.le.ge_iff_eq' (fun _ => N.smul_mem r)

variable {r}
/-
**IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul : IsSMulRegul
ar M r -> (IsSMulRegular (M ⧸ N) r ↔ r • ⊤ ⊓ N <= r • N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isSMulRegular_on_quot_iff_lsmul_comap_le`：isSMulRegular_on_quot_iff_lsmu
l_comap_le : IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) <= N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_le_map_iff_of_injective`：map_le_map_iff_of_injective (p q 
: Submodule R M) : p.map f <= q.map f ↔ p <= q
· 使用引理 `LinearMap.lsmul_eq_distribSMultoLinearMap`：lsmul_eq_distribSMultoLinearM
ap (r : R) : lsmul R M r = DistribSMul.toLinearMap R M r
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul :
    IsSMulRegular M r → (IsSMulRegular (M ⧸ N) r ↔ r • ⊤ ⊓ N ≤ r • N) := by
  intro (h : Function.Injective (DistribSMul.toLinearMap R M r))
  rw [isSMulRegular_on_quot_iff_lsmul_comap_le, ← map_le_map_iff_of_injective h,
    ← LinearMap.lsmul_eq_distribSMultoLinearMap,
    map_comap_eq, LinearMap.range_eq_map]; rfl
/-
**isSMulRegular_of_ker_lsmul_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_of_ker_lsmul_eq_bot (h : LinearMap.ker (LinearMap.lsmul R M 
r) = ⊥) : IsSMulRegular M r
参数：h : LinearMap.ker (LinearMap.lsmul R M r) = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isSMulRegular_iff_ker_lsmul_eq_bot`：isSMulRegular_iff_ker_lsmul_eq_bot :
 IsSMulRegular M r ↔ LinearMap.ker (LinearMap.lsmul R M r) = ⊥
-/
lemma isSMulRegular_of_ker_lsmul_eq_bot
    (h : LinearMap.ker (LinearMap.lsmul R M r) = ⊥) :
    IsSMulRegular M r :=
  (isSMulRegular_iff_ker_lsmul_eq_bot M r).mpr h

variable {N} in
/-
**smul_top_inf_eq_smul_of_isSMulRegular_on_quot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_top_inf_eq_smul_of_isSMulRegular_on_quot : IsSMulRegular (M ⧸ N) r ->
 r • ⊤ ⊓ N <= r • N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isSMulRegular_on_quot_iff_lsmul_comap_le`：isSMulRegular_on_quot_iff_lsmu
l_comap_le : IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) <= N
-/
lemma smul_top_inf_eq_smul_of_isSMulRegular_on_quot :
    IsSMulRegular (M ⧸ N) r → r • ⊤ ⊓ N ≤ r • N := by
  convert! map_mono ∘ (isSMulRegular_on_quot_iff_lsmul_comap_le N r).mp using 2
  exact Eq.trans (congrArg (· ⊓ N) (map_top _)) (map_comap_eq _ _).symm

-- Who knew this didn't rely on exactness at the right!?
set_option backward.isDefEq.respectTransparency.types false in
open Function in
/-
**QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last** 是 Mathl
ib 中的一个引理，位于命名空间 ``。
形式化陈述：QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last {M'''
} [AddCommGroup M'''] [Module R M'''] {r : R} {f₁ : M ->ₗ[R] M'} {f₂ : M' ->ₗ[R]
 M''} {f₃ : M'' ->ₗ[R] M'''} (h₁₂ : Exact f₁ f₂) (h₂₃ : Exact f₂ f₃) (h : IsSMul
Regular M''' r) : Exact (map r f₁) (map r f₂)
参数：h₁₂ : Exact f₁ f₂；h₂₃ : Exact f₂ f₃；h : IsSMulRegular M''' r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSMulRegular.of_injective`：IsSMulRegular.of_injective {R M : Type*} [SM
ul R M] {N F} [SMul R N] [FunLike F M N] [MulActionHomClass F R M N] (f : F) {r 
: R} (h1 : Funct…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.ker_liftQ_eq_bot'`：ker_liftQ_eq_bot' (f : M ->ₛₗ[τ₁₂] M₂) (h :
 p = ker f) : ker (p.liftQ f (le_of_eq h)) = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Exact.exact_mapQ_iff`：∀ {R : Type u_1} {M : Type u_2} {N : Type
 u_4} {P : Type u_6} [inst : Ring R] [inst_1 : AddCommGroup M]   [inst_2 : AddCo
mmGroup N] [inst_3 …
· 使用定理 `Submodule.map_pointwise_smul`：map_pointwise_smul (r : R) (N : Submodule 
R M) (f : M ->ₗ[R] M') : (r • N).map f = r • N.map f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用引理 `smul_top_inf_eq_smul_of_isSMulRegular_on_quot`：smul_top_inf_eq_smul_of_i
sSMulRegular_on_quot : IsSMulRegular (M ⧸ N) r -> r • ⊤ ⊓ N <= r • N
-/
lemma QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    {M'''} [AddCommGroup M'''] [Module R M''']
    {r : R} {f₁ : M →ₗ[R] M'} {f₂ : M' →ₗ[R] M''} {f₃ : M'' →ₗ[R] M'''}
    (h₁₂ : Exact f₁ f₂) (h₂₃ : Exact f₂ f₃) (h : IsSMulRegular M''' r) :
    Exact (map r f₁) (map r f₂) :=
  suffices IsSMulRegular (M'' ⧸ LinearMap.range f₂) r by
    dsimp [map, mapQLinear]
    rw [Exact.exact_mapQ_iff h₁₂, map_pointwise_smul, Submodule.map_top, inf_comm]
    exact smul_top_inf_eq_smul_of_isSMulRegular_on_quot this
  h.of_injective _ <| LinearMap.ker_eq_bot.mp <|
    ker_liftQ_eq_bot' _ _ h₂₃.linearMap_ker_eq.symm

end CommRing

