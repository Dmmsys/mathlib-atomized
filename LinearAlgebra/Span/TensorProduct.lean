/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity

/-!
# The interaction of linear span and tensor product for mixed scalars.
-/

@[expose] public section

open Function TensorProduct

namespace Submodule

variable {R : Type*} (A : Type*) {M : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  (p : Submodule R M)

/-- If `A` is an `R`-algebra and `p` is an `R`-submodule of an `A`-module `M`, this is the natural
surjection `A ⊗[R] p → span A p`.

See also `Submodule.tensorEquivSpan`. -/
/-
**Submodule.tensorToSpan** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：tensorToSpan : A otimes[R] p ->ₗ[A] span A (p : Set M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is an `R`-algebra and `p` is an `R`-submodule of an `A`-module `M`, this 
is the natural
surjection `A ⊗[R] p → span A p`.

See also `Submodule.tensorEquivSpan`.
-/
def tensorToSpan : A ⊗[R] p →ₗ[A] span A (p : Set M) :=
  AlgebraTensorModule.lift
    { toFun a := a • p.inclusionSpan A
      map_add' a b := add_smul a b _
      map_smul' a b := smul_assoc a b _ }
/-
**Submodule.tensorToSpan_apply_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {M : Type u_3} [inst : CommSemiring R] [in
st_1 : CommSemiring A] [inst_2 : Algebra R A]   [inst_3 : AddCommMonoid M] [inst
_4 : _root_.Module R M] [inst_5 : _root_.Module A M] [inst_6 : IsScalarTower R A
 M]   (p : Submodule R M) (a : A) (x : ↥p), ↑((Submodule.tensorToSpan A p) (a ⊗ₜ
[R] x)) = a • ↑x
参数：A : Type u_2；p : Submodule R M；a : A；x : ↥p；(Submodule.tensorToSpan A p) (a ⊗
ₜ[R] x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma tensorToSpan_apply_tmul (a : A) (x : p) :
    p.tensorToSpan A (a ⊗ₜ x) = a • (x : M) :=
  rfl
/-
**Submodule.surjective_tensorToSpan** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：surjective_tensorToSpan : Surjective (p.tensorToSpan A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_span_iff_linearCombination`：mem_span_iff_linearCombination (
s : Set M) (x : M) : x in span R s ↔ exists l : s ->₀ R, linearCombination R (↑)
 l = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subtype_apply`：subtype_apply (x : p) : p.subtype x = x
-/
lemma surjective_tensorToSpan : Surjective (p.tensorToSpan A) := by
  intro v
  obtain ⟨f, hf⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp v.property
  use f.sum fun x a ↦ a ⊗ₜ x
  rw [map_finsuppSum, Subtype.ext_iff, ← Submodule.subtype_apply, map_finsuppSum]
  simpa using! hf

variable [Algebra.IsEpi R A] [Module.Flat R A]

open Module.Flat LinearMap in
/-
**Submodule.injective_tensorToSpan** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：injective_tensorToSpan : Injective (p.tensorToSpan A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `Algebra.injective_lift_lsmul`：injective_lift_lsmul : Injective (lift <| 
LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M))
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用引理 `Submodule.injective_inclusionSpan`：injective_inclusionSpan : Injective (
p.inclusionSpan S)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Submodule.inclusionSpan_apply_coe`：∀ {R : Type u_1} {M : Type u_4} (S : 
Type u_7) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M] [inst_3 : Semir…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.restrictScalarsₗ_apply`：∀ (R : Type u_14) (S : Type u_15) (M :
 Type u_16) (N : Type u_17) [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 
: AddCommMonoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
-/
lemma injective_tensorToSpan : Injective (p.tensorToSpan A) := by
  let f : A ⊗[R] (span A (p : Set M)) →ₗ[A] span A (p : Set M) :=
    AlgebraTensorModule.lift <| (restrictScalarsₗ R A _ _ A) ∘ₗ lsmul A (span A (p : Set M))
  let g : A ⊗[R] p →ₗ[R] A ⊗[R] span A (p : Set M) := (p.inclusionSpan A).lTensor A
  have hf : Injective f := Algebra.injective_lift_lsmul R A _
  have hg : Injective g := lTensor_preserves_injective_linearMap _ (p.injective_inclusionSpan A)
  have : p.tensorToSpan A = f.restrictScalars R ∘ₗ g := by ext; simp [tensorToSpan, f, g]
  rw [← LinearMap.coe_restrictScalars R, this, coe_comp]
  exact hf.comp hg

/-- If `A` is a flat epi `R`-algebra and `p` is an `R`-submodule of an `A`-module `M` then the
natural surjection from `A ⊗[R] p` to `span A p` is an equivalence. -/
/-
**Submodule.tensorEquivSpan** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：tensorEquivSpan : A otimes[R] p ≃ₗ[A] span A (p : Set M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a flat epi `R`-algebra and `p` is an `R`-submodule of an `A`-module `M
` then the
natural surjection from `A ⊗[R] p` to `span A p` is an equivalence.
-/
noncomputable def tensorEquivSpan : A ⊗[R] p ≃ₗ[A] span A (p : Set M) :=
  .ofBijective (p.tensorToSpan A) ⟨p.injective_tensorToSpan A, p.surjective_tensorToSpan A⟩
/-
**Submodule.tensorEquivSpan_apply_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {M : Type u_3} [inst : CommSemiring R] [in
st_1 : CommSemiring A] [inst_2 : Algebra R A]   [inst_3 : AddCommMonoid M] [inst
_4 : _root_.Module R M] [inst_5 : _root_.Module A M] [inst_6 : IsScalarTower R A
 M]   (p : Submodule R M) [inst_7 : Algebra.IsEpi R A] [inst_8 : Module.Flat R A
] (a : A) (x : ↥p),   ↑((Submodule.tensorEquivSpan A p) (a ⊗ₜ[R] x)) = a • ↑x
参数：A : Type u_2；p : Submodule R M；a : A；x : ↥p；(Submodule.tensorEquivSpan A p) (
a ⊗ₜ[R] x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma tensorEquivSpan_apply_tmul (a : A) (x : p) :
    p.tensorEquivSpan A (a ⊗ₜ x) = a • (x : M) :=
  rfl

variable (R) in
/-- If `A` is a flat epi `R`-algebra and `s` is a subset of an `A`-module `M` then the natural
surjection from `A ⊗[R] span R s` to `span A s` is an equivalence. -/
/-
**Submodule.tensorSpanEquivSpan** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：tensorSpanEquivSpan (s : Set M) : A otimes[R] span R s ≃ₗ[A] span A s
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a flat epi `R`-algebra and `s` is a subset of an `A`-module `M` then t
he natural
surjection from `A ⊗[R] span R s` to `span A s` is an equivalence.
-/
noncomputable def tensorSpanEquivSpan (s : Set M) : A ⊗[R] span R s ≃ₗ[A] span A s :=
  ((span R s).tensorEquivSpan A).trans <| .ofEq _ _ <| span_span_of_tower R A s
/-
**Submodule.coe_tensorSpanEquivSpan_apply_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {M : Type u_3} [inst : CommSemiring R] [in
st_1 : CommSemiring A] [inst_2 : Algebra R A]   [inst_3 : AddCommMonoid M] [inst
_4 : _root_.Module R M] [inst_5 : _root_.Module A M] [inst_6 : IsScalarTower R A
 M]   [inst_7 : Algebra.IsEpi R A] [inst_8 : Module.Flat R A] {s : Set M} (a : A
) (x : ↥(Submodule.span R s)),   ↑((Submodule.tensorSpanEquivSpan R A s) (a ⊗ₜ[R
] x)) = a • ↑x
参数：A : Type u_2；a : A；x : ↥(Submodule.span R s)；(Submodule.tensorSpanEquivSpan R
 A s) (a ⊗ₜ[R] x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma coe_tensorSpanEquivSpan_apply_tmul {s : Set M} (a : A) (x : span R s) :
    tensorSpanEquivSpan R A s (a ⊗ₜ x) = a • (x : M) :=
  rfl

end CommSemiring

section CommRing

open Module

variable [CommRing R] [CommRing A] [Nontrivial A]
  [Algebra R A] [Algebra.IsEpi R A] [Module.Flat R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (p : Submodule R M) [Free R p] [Module.Finite R p]

/-
**Submodule.finrank_span_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {M : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [Nontrivial A]   [inst_3 : Algebra R A] [Algebra.IsEpi R A] [Modu
le.Flat R A] [inst_6 : AddCommGroup M] [inst_7 : _root_.Module R M]   [inst_8 : 
_root_.Module A M] [IsScalarTower R A M] (p : Submodule R M) [Module.Free R ↥p] 
[Module.Finite R ↥p],   Module.finrank A ↥(Submodule.span A ↑p) = Module.finrank
 R ↥p
参数：A : Type u_2；p : Submodule R M；Submodule.span A ↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_subsingleton`：∀ {R : Type u} {M : Type v} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsingleton R],
 Module.finrank R…
· 使用定理 `Algebra.subsingleton`：Algebra.subsingleton (R : Type u) (A : Type v) [Co
mmSemiring R] [Semiring A] [Algebra R A] [Subsingleton R] : Subsingleton A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
-/
@[simp] lemma finrank_span_eq_finrank :
    finrank A (span A (p : Set M)) = finrank R p := by
  rcases subsingleton_or_nontrivial R; · simp [Algebra.subsingleton R A]
  let ι := Free.ChooseBasisIndex R p
  let b₁ : Basis ι R p := Free.chooseBasis R p
  let b₂ : Basis ι A (span A (p : Set M)) := (b₁.baseChange A).map <| p.tensorEquivSpan A
  rw [finrank_eq_card_basis b₁, finrank_eq_card_basis b₂]

variable (R) in
/-
**Submodule.finrank_span_eq_finrank_span** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：finrank_span_eq_finrank_span [IsPrincipalIdealRing R] [IsDomain R] [IsTors
ionFree R M] (s : Set M) [Module.Finite R (span R s)] : finrank A (span A s) = f
inrank R (span R s)
参数：s : Set M；span R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `Submodule.finrank_span_eq_finrank`：∀ {R : Type u_1} (A : Type u_2) {M : 
Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [Nontrivial A]   [inst_3 : A
lgebra R A] [Algebra.Is…
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
-/
lemma finrank_span_eq_finrank_span [IsPrincipalIdealRing R] [IsDomain R] [IsTorsionFree R M]
    (s : Set M) [Module.Finite R (span R s)] :
    finrank A (span A s) = finrank R (span R s) := by
  rw [← span_span_of_tower R, finrank_span_eq_finrank]

end CommRing

end Submodule

