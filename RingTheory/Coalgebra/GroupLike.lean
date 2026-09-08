/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Coalgebra.Equiv
public import Mathlib.RingTheory.Flat.Domain

/-!
# Group-like elements in a coalgebra

This file defines group-like elements in a coalgebra, i.e. elements `a` such that `ε a = 1` and
`Δ a = a ⊗ₜ a`.

## Main declarations

* `IsGroupLikeElem`: Predicate for an element in a coalgebra to be group-like.
* `linearIndepOn_isGroupLikeElem`: Group-like elements over a domain are linearly independent.
-/

@[expose] public section

open Coalgebra Function Module TensorProduct

variable {F R A B : Type*}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Coalgebra R A]
  [Module R B] [Coalgebra R B] {a b : A}

variable (R) in
/-- A group-like element in a coalgebra is an element `a` such that `ε(a) = 1` and `Δ(a) = a ⊗ₜ a`,
where `ε` and `Δ` are the counit and comultiplication respectively. -/
@[mk_iff]
/-
**IsGroupLikeElem** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：IsGroupLikeElem (a : A) : Prop where /-- A group-like element `a` satisfie
s `ε(a) = 1`. -/ counit_eq_one : counit (R
参数：a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group-like element in a coalgebra is an element `a` such that `ε(a) = 1` and `
Δ(a) = a ⊗ₜ a`,
where `ε` and `Δ` are the counit and comultiplication respectively.
-/
structure IsGroupLikeElem (a : A) : Prop where
  /-- A group-like element `a` satisfies `ε(a) = 1`. -/
  counit_eq_one : counit (R := R) a = 1
  /-- A group-like element `a` satisfies `Δ(a) = a ⊗ₜ a`. -/
  comul_eq_tmul_self : comul a = a ⊗ₜ[R] a

attribute [simp] IsGroupLikeElem.counit_eq_one IsGroupLikeElem.comul_eq_tmul_self
/-
**isGroupLikeElem_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_2} [inst : CommSemiring R] {r : R}, IsGroupLikeElem R r ↔ r 
= 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma isGroupLikeElem_self {r : R} : IsGroupLikeElem R r ↔ r = 1 := by
  simp +contextual [isGroupLikeElem_iff]
/-
**IsGroupLikeElem.ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGroupLikeElem.ne_zero [Nontrivial R] (ha : IsGroupLikeElem R a) : a != 0
参数：ha : IsGroupLikeElem R a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsGroupLikeElem.ne_zero [Nontrivial R] (ha : IsGroupLikeElem R a) : a ≠ 0 := by
  rintro rfl; simpa using ha.counit_eq_one

/-- A coalgebra homomorphism sends group-like elements to group-like elements. -/
/-
**IsGroupLikeElem.map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGroupLikeElem.map [FunLike F A B] [CoalgHomClass F R A B] (f : F) (ha : 
IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where counit_eq_one
参数：f : F；ha : IsGroupLikeElem R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoalgHomClass.counit_comp_apply`：counit_comp_apply (f : F) (x : A) : cou
nit (f x) = counit (R
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoalgHomClass.map_comp_comul_apply`：map_comp_comul_apply (f : F) (x : A)
 : TensorProduct.map f f (σ₁₂
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A coalgebra homomorphism sends group-like elements to group-like elements.
-/
lemma IsGroupLikeElem.map [FunLike F A B] [CoalgHomClass F R A B] (f : F)
    (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where
  counit_eq_one := by rw [CoalgHomClass.counit_comp_apply, ha.counit_eq_one]
  comul_eq_tmul_self := by rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]; simp

/-- A coalgebra isomorphism preserves group-like elements. -/
/-
**isGroupLikeElem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {F : Type u_1} {R : Type u_2} {A : Type u_3} {B : Type u_4} [inst : Comm
Semiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMonoid B] [inst_3 : _r
oot_.Module R A] [inst_4 : Coalgebra R A] [inst_5 : _root_.Module R B]   [inst_6
 : Coalgebra R B] {a : A} [inst_7 : EquivLike F A B] [CoalgEquivClass F R A B] (
f : F),   IsGroupLikeElem R (f a) ↔ IsGroupLikeElem R a
参数：f : F；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsGroupLikeElem.map`：IsGroupLikeElem.map [FunLike F A B] [CoalgHomClass 
F R A B] (f : F) (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where coun
it_eq_one
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquiv.instCoalgEquivClass`：∀ {R : Type u_1} {A : Type u_2} {B : Typ
e u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMon
oid B] [inst_3 : _ro…
· 使用定理 `CoalgEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃ₗc[R] B) (x) : e.s
ymm (e x) = x

--- 原说明 ---
A coalgebra isomorphism preserves group-like elements.
-/
@[simp] lemma isGroupLikeElem_map_equiv [EquivLike F A B] [CoalgEquivClass F R A B] (f : F) :
    IsGroupLikeElem R (f a) ↔ IsGroupLikeElem R a where
  mp ha := (CoalgEquivClass.toCoalgEquiv f).symm_apply_apply a ▸ ha.map _
  mpr := .map f

variable (R A) in
/-- The type of group-like elements in a coalgebra. -/
@[ext]
/-
**GroupLike** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) →   (A : Type u_3) →     [inst : CommSemiring R] → [inst_1 
: AddCommMonoid A] → [inst_2 : _root_.Module R A] → [Coalgebra R A] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of group-like elements in a coalgebra.
-/
structure GroupLike where
  /-- The underlying element of a group-like element. -/
  val : A
  isGroupLikeElem_val : IsGroupLikeElem R val

namespace GroupLike

initialize_simps_projections GroupLike (as_prefix val)

attribute [simp] isGroupLikeElem_val

attribute [coe] val

/-
**GroupLike.instCoeOut** 是 Mathlib 中的一个实例，位于命名空间 `GroupLike`。
形式化陈述：instCoeOut : CoeOut (GroupLike R A) A where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeOut : CoeOut (GroupLike R A) A where coe := val
/-
**GroupLike.val_injective** 是 Mathlib 中的一个引理，位于命名空间 `GroupLike`。
形式化陈述：val_injective : Injective (val : GroupLike R A -> A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `GroupLike.isGroupLikeElem_val`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] (…
-/
lemma val_injective : Injective (val : GroupLike R A → A) := by rintro ⟨a, ha⟩; congr!
/-
**GroupLike.val_inj** 是 Mathlib 中的一个定理，位于命名空间 `GroupLike`。
形式化陈述：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] [inst_1 : AddCommM
onoid A] [inst_2 : _root_.Module R A]   [inst_3 : Coalgebra R A] {a b : GroupLik
e R A}, ↑a = ↑b ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `GroupLike.val_injective`：val_injective : Injective (val : GroupLike R A 
-> A)
-/
@[simp, norm_cast] lemma val_inj {a b : GroupLike R A} : a.val = b.val ↔ a = b :=
  val_injective.eq_iff

/-- Identity equivalence between `GroupLike R A` and `{a : A // IsGroupLikeElem R a}`. -/
@[simps]
/-
**GroupLike.valEquiv** 是 Mathlib 中的一个定义，位于命名空间 `GroupLike`。
形式化陈述：valEquiv : GroupLike R A ≃ Subtype (IsGroupLikeElem R : A -> Prop) where t
oFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupLike.isGroupLikeElem_val`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] (…

--- 原说明 ---
Identity equivalence between `GroupLike R A` and `{a : A // IsGroupLikeElem R a}
`.
-/
def valEquiv : GroupLike R A ≃ Subtype (IsGroupLikeElem R : A → Prop) where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GroupLike
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A] [Coalgebra R A]
  [IsTorsionFree R A]

open Submodule in
/-- Group-like elements over a domain are linearly independent. -/
/-
**linearIndepOn_isGroupLikeElem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndepOn_isGroupLikeElem : LinearIndepOn R id {a : A | IsGroupLikeEle
m R a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `linearIndepOn_iff_linearIndepOn_finset`：linearIndepOn_iff_linearIndepOn_
finset : LinearIndepOn R v s ↔ forall t : Finset ι, ↑t subseteq s -> LinearIndep
On R v t where mp hv t hts
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用引理 `LinearIndepOn.id_insert'`：LinearIndepOn.id_insert' {s : Set M} {x : M} (
hs : LinearIndepOn R id s) (hx : forall r : R, r • x in Submodule.span R s -> r 
= 0) : LinearI…
· 使用定理 `LinearIndepOn.tmul_of_isDomain`：∀ {R : Type u_1} {M : Type u_2} {N : Typ
e u_3} [inst : CommRing R] [IsDomain R] [inst_2 : AddCommGroup M]   [inst_3 : _r
oot_.Module R M] [in…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
Group-like elements over a domain are linearly independent.
-/
lemma linearIndepOn_isGroupLikeElem : LinearIndepOn R id {a : A | IsGroupLikeElem R a} := by
  classical
  -- We show that any finset `s` of group-like elements is linearly independent.
  rw [linearIndepOn_iff_linearIndepOn_finset]
  rintro s hs
  -- For this, we do induction on `s`.
  induction s using Finset.cons_induction with
  -- The case `s = ∅` is trivial.
  | empty => simp
  -- Let's deal with the `s ∪ {a}` case.
  | cons a s has ih =>
  simp only [Finset.cons_eq_insert, Finset.coe_insert, Set.subset_def, Set.mem_insert_iff,
    Finset.mem_coe, Set.mem_ofPred_eq, forall_eq_or_imp] at hs
  obtain ⟨ha, hs⟩ := hs
  specialize ih hs
  -- Assume that there is some `c : A → R` and `d : R` such that `∑ x ∈ s, c x • x = d • a`.
  -- We want to prove `d = 0` and `∀ x ∈ s, c x = 0`.
  rw [Finset.coe_cons]
  refine ih.id_insert' ?_
  simp only [mem_span_finset, forall_exists_index, and_imp]
  rintro d c - hc
  -- `x ⊗ y` over `x, y ∈ s` are linearly independent since `s` is linearly independent and
  -- `R` is a domain.
  replace ih := ih.tmul_of_isDomain ih
  simp_rw [← Finset.coe_product, linearIndepOn_finset_iffₛ, id] at ih
  -- Tensoring the equality `∑ x ∈ s, c x • x = d • a` with itself, we get by linear independence
  -- that `c x ^ 2 = d * c x` and `c x * c y = 0` for `x ≠ y`.
  have key := calc
        ∑ x ∈ s, ∑ y ∈ s, (if x = y then d * c x else 0) • x ⊗ₜ[R] y
    _ = d • ∑ x ∈ s, c x • x ⊗ₜ[R] x := by simp [Finset.smul_sum, mul_smul]
    _ = d • comul (d • a) := by rw [← hc]; simp +contextual [(hs _ _).comul_eq_tmul_self]
    _ = (d • a) ⊗ₜ (d • a) := by simp [ha.comul_eq_tmul_self, smul_tmul, tmul_smul, -neg_smul]
    _ = ∑ x ∈ s, ∑ y ∈ s, (c x * c y) • x ⊗ₜ[R] y := by
      simp_rw [← hc, sum_tmul, smul_tmul, Finset.smul_sum, tmul_sum, tmul_smul, mul_smul]
  simp_rw [← Finset.sum_product'] at key
  apply ih at key
  -- Therefore, `c x = 0` for all `x ∈ s`.
  replace key x (hx : x ∈ s) : c x = 0 := by
    -- Otherwise, we deduce from `key` that `c y = 0` for any `y ≠ x` with `y ∈ s`.
    by_contra! hcx
    have hcy (y) (hys : y ∈ s) (hyx : y ≠ x) : c y = 0 := by
      simpa [*] using (key (y, x) (by simp [*])).symm
    -- Then substitute this into `hc` to get `c x • x = d • a`.
    rw [Finset.sum_eq_single x (by simp +contextual [hcy]) (by simp [hx])] at hc
    -- But `key` also says that `c x = d`.
    have hcxa : d = c x := mul_left_injective₀ hcx (by simpa using (key (x, x) (by simp [*])))
    -- So `x = a`...
    obtain rfl : x = a := by rwa [hcxa, smul_right_inj hcx] at hc
    -- ... which contradicts `x ∈ s` and `a ∉ s`.
    contradiction
  -- We are now done, since `d • a = ∑ x ∈ s, c x • x = 0`
  simp_all [ha.ne_zero, eq_comm]

/-- Group-like elements over a domain are linearly independent. -/
/-
**linearIndep_groupLikeVal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndep_groupLikeVal : LinearIndependent R (GroupLike.val (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用引理 `linearIndepOn_isGroupLikeElem`：linearIndepOn_isGroupLikeElem : LinearInd
epOn R id {a : A | IsGroupLikeElem R a}

--- 原说明 ---
Group-like elements over a domain are linearly independent.
-/
lemma linearIndep_groupLikeVal : LinearIndependent R (GroupLike.val (R := R) (A := A)) := by
  simpa using! (linearIndependent_equiv GroupLike.valEquiv).2 linearIndepOn_isGroupLikeElem

end CommRing

