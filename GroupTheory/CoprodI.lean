/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Joachim Breitner
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# The coproduct (a.k.a. the free product) of groups or monoids

Given an `ι`-indexed family `M` of monoids,
we define their coproduct (a.k.a. free product) `Monoid.CoprodI M`.
As usual, we use the suffix `I` for an indexed (co)product,
leaving `Coprod` for the coproduct of two monoids.

When `ι` and all `M i` have decidable equality,
the free product bijects with the type `Monoid.CoprodI.Word M` of reduced words.
This bijection is constructed
by defining an action of `Monoid.CoprodI M` on `Monoid.CoprodI.Word M`.

When `M i` are all groups, `Monoid.CoprodI M` is also a group
(and the coproduct in the category of groups).

## Main definitions

- `Monoid.CoprodI M`: the free product, defined as a quotient of a free monoid.
- `Monoid.CoprodI.of {i} : M i →* Monoid.CoprodI M`.
- `Monoid.CoprodI.lift : (∀ {i}, M i →* N) ≃ (Monoid.CoprodI M →* N)`: the universal property.
- `Monoid.CoprodI.Word M`: the type of reduced words.
- `Monoid.CoprodI.Word.equiv M : Monoid.CoprodI M ≃ word M`.
- `Monoid.CoprodI.NeWord M i j`: an inductive description of non-empty words
  with first letter from `M i` and last letter from `M j`,
  together with an API (`singleton`, `append`, `head`, `tail`, `to_word`, `Prod`, `inv`).
  Used in the proof of the Ping-Pong-lemma.
- `Monoid.CoprodI.lift_injective_of_ping_pong`: The Ping-Pong-lemma,
  proving injectivity of the `lift`. See the documentation of that theorem for more information.

## Remarks

There are many answers to the question "what is the coproduct of a family `M` of monoids?",
and they are all equivalent but not obviously equivalent.
We provide two answers.
The first, almost tautological answer is given by `Monoid.CoprodI M`,
which is a quotient of the type of words in the alphabet `Σ i, M i`.
It's straightforward to define and easy to prove its universal property.
But this answer is not completely satisfactory,
because it's difficult to tell when two elements `x y : Monoid.CoprodI M` are distinct
since `Monoid.CoprodI M` is defined as a quotient.

The second, maximally efficient answer is given by `Monoid.CoprodI.Word M`.
An element of `Monoid.CoprodI.Word M` is a word in the alphabet `Σ i, M i`,
where the letter `⟨i, 1⟩` doesn't occur and no adjacent letters share an index `i`.
Since we only work with reduced words, there is no need for quotienting,
and it is easy to tell when two elements are distinct.
However it's not obvious that this is even a monoid!

We prove that every element of `Monoid.CoprodI M` can be represented by a unique reduced word,
i.e. `Monoid.CoprodI M` and `Monoid.CoprodI.Word M` are equivalent types.
This means that `Monoid.CoprodI.Word M` can be given a monoid structure,
and it lets us tell when two elements of `Monoid.CoprodI M` are distinct.

There is also a completely tautological, maximally inefficient answer
given by `MonCat.Colimits.ColimitType`.
Whereas `Monoid.CoprodI M` at least ensures that
(any instance of) associativity holds by reflexivity,
in this answer associativity holds because of quotienting.
Yet another answer, which is constructively more satisfying,
could be obtained by showing that `Monoid.CoprodI.Rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/

@[expose] public section


open Set

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)]

/-- A relation on the free monoid on alphabet `Σ i, M i`,
relating `⟨i, 1⟩` with `1` and `⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`. -/
/-
**Monoid.CoprodI.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `Monoid.CoprodI`。
形式化陈述：{ι : Type u_1} →   (M : ι → Type u_2) → [(i : ι) → Monoid (M i)] → FreeMon
oid ((i : ι) × M i) → FreeMonoid ((i : ι) × M i) → Prop
参数：M : ι → Type u_2；i : ι；M i；(i : ι) × M i；(i : ι) × M i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation on the free monoid on alphabet `Σ i, M i`,
relating `⟨i, 1⟩` with `1` and `⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`.
-/
inductive Monoid.CoprodI.Rel : FreeMonoid (Σ i, M i) → FreeMonoid (Σ i, M i) → Prop
  | of_one (i : ι) : Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, 1⟩) 1
  | of_mul {i : ι} (x y : M i) :
    Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, x⟩ * FreeMonoid.of ⟨i, y⟩) (FreeMonoid.of ⟨i, x * y⟩)

/-- The free product (categorical coproduct) of an indexed family of monoids. -/
/-
**Monoid.CoprodI** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Monoid.CoprodI : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free product (categorical coproduct) of an indexed family of monoids.
-/
def Monoid.CoprodI : Type _ := (conGen (Monoid.CoprodI.Rel M)).Quotient
deriving Monoid, Inhabited

namespace Monoid.CoprodI

/-- The type of reduced words. A reduced word cannot contain a letter `1`, and no two adjacent
letters can come from the same summand. -/
@[ext]
/-
**Monoid.CoprodI.Word** 是 Mathlib 中的一个归纳类型，位于命名空间 `Monoid.CoprodI`。
形式化陈述：{ι : Type u_1} → (M : ι → Type u_2) → [(i : ι) → Monoid (M i)] → Type (max
 u_1 u_2)
参数：M : ι → Type u_2；i : ι；M i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of reduced words. A reduced word cannot contain a letter `1`, and no tw
o adjacent
letters can come from the same summand.
-/
structure Word where
  /-- A `Word` is a `List (Σ i, M i)`, such that `1` is not in the list, and no
  two adjacent letters are from the same summand -/
  toList : List (Σ i, M i)
  /-- A reduced word does not contain `1` -/
  ne_one : ∀ l ∈ toList, Sigma.snd l ≠ 1
  /-- Adjacent letters are not from the same summand. -/
  chain_ne : toList.IsChain fun l l' => Sigma.fst l ≠ Sigma.fst l'

variable {M}

/-- The inclusion of a summand into the free product. -/
/-
**Monoid.CoprodI.of** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI`。
形式化陈述：of {i : ι} : M i ->* CoprodI M where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a summand into the free product.
-/
def of {i : ι} : M i →* CoprodI M where
  toFun x := Con.mk' _ (FreeMonoid.of <| Sigma.mk i x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_one i))
  map_mul' x y := Eq.symm <| (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_mul x y))
/-
**Monoid.CoprodI.of_apply** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：of_apply {i} (m : M i) : of m = Con.mk' _ (FreeMonoid.of <| Sigma.mk i m)
参数：m : M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_apply {i} (m : M i) : of m = Con.mk' _ (FreeMonoid.of <| Sigma.mk i m) :=
  rfl

variable {N : Type*} [Monoid N]

set_option backward.isDefEq.respectTransparency false in
/-- See note [partially-applied ext lemmas]. -/
@[ext 1100] -- This needs a higher `ext` priority
/-
**Monoid.CoprodI.ext_hom** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：ext_hom (f g : CoprodI M ->* N) (h : forall i, f.comp (of : M i ->* _) = g
.comp of) : f = g
参数：f g : CoprodI M ->* N；h : forall i, f.comp (of : M i ->* _) = g.comp of。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.cancel_right`：MonoidHom.cancel_right [MulOne M] [MulOne N] [Mu
lOne P] {g₁ g₂ : N ->* P} {f : M ->* N} (hf : Function.Surjective f) : g₁.comp f
 = g₂.comp f…
· 使用定理 `Con.mk'_surjective`：∀ {M : Type u_1} [inst : MulOneClass M] {c : Con M},
 Function.Surjective ⇑c.mk'
· 使用定理 `FreeMonoid.hom_eq`：hom_eq ⦃f g : FreeMonoid α ->* M⦄ (h : forall x, f (o
f x) = g (of x)) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.CoprodI.of_apply`：of_apply {i} (m : M i) : of m = Con.mk' _ (Free
Monoid.of <| Sigma.mk i m)

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem ext_hom (f g : CoprodI M →* N) (h : ∀ i, f.comp (of : M i →* _) = g.comp of) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    FreeMonoid.hom_eq fun ⟨i, x⟩ => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← of_apply]
      unfold CoprodI
      rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, h]

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, characterizing it as a categorical coproduct. -/
@[simps symm_apply]
/-
**Monoid.CoprodI.lift** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI`。
形式化陈述：lift : (forall i, M i ->* N) ≃ (CoprodI M ->* N) where toFun fi
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map out of the free product corresponds to a family of maps out of the summand
s. This is the
universal property of the free product, characterizing it as a categorical copro
duct.
-/
def lift : (∀ i, M i →* N) ≃ (CoprodI M →* N) where
  toFun fi :=
    Con.lift _ (FreeMonoid.lift fun p : Σ i, M i => fi p.fst p.snd) <|
      Con.conGen_le.2 <| fun _ _ => by
        simp_rw [Con.ker_rel]
        rintro (i | ⟨x, y⟩) <;> simp
  invFun f _ := f.comp of
  left_inv := by
    intro fi
    ext i x
    rfl
  right_inv := by
    intro f
    ext i x
    rfl

@[simp]
/-
**Monoid.CoprodI.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：lift_comp_of {N} [Monoid N] (fi : forall i, M i ->* N) i : (lift fi).comp 
of = fi i
参数：fi : forall i, M i ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem lift_comp_of {N} [Monoid N] (fi : ∀ i, M i →* N) i : (lift fi).comp of = fi i :=
  congr_fun (lift.symm_apply_apply fi) i

@[simp]
/-
**Monoid.CoprodI.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：lift_of {N} [Monoid N] (fi : forall i, M i ->* N) {i} (m : M i) : lift fi 
(of m) = fi i m
参数：fi : forall i, M i ->* N；m : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Monoid.CoprodI.lift_comp_of`：lift_comp_of {N} [Monoid N] (fi : forall i,
 M i ->* N) i : (lift fi).comp of = fi i
-/
theorem lift_of {N} [Monoid N] (fi : ∀ i, M i →* N) {i} (m : M i) : lift fi (of m) = fi i m :=
  DFunLike.congr_fun (lift_comp_of ..) m

@[simp]
/-
**Monoid.CoprodI.lift_comp_of'** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：lift_comp_of' {N} [Monoid N] (f : CoprodI M ->* N) : lift (fun i => f.comp
 (of (i
参数：f : CoprodI M ->* N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem lift_comp_of' {N} [Monoid N] (f : CoprodI M →* N) :
    lift (fun i ↦ f.comp (of (i := i))) = f :=
  lift.apply_symm_apply f

@[simp]
/-
**Monoid.CoprodI.lift_of'** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：lift_of' : lift (fun i => (of : M i ->* CoprodI M)) = .id (CoprodI M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.lift_comp_of'`：lift_comp_of' {N} [Monoid N] (f : CoprodI 
M ->* N) : lift (fun i => f.comp (of (i
-/
theorem lift_of' : lift (fun i ↦ (of : M i →* CoprodI M)) = .id (CoprodI M) :=
  lift_comp_of' (.id _)
/-
**Monoid.CoprodI.of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：of_leftInverse [DecidableEq ι] (i : ι) : Function.LeftInverse (lift <| Pi.
mulSingle i (MonoidHom.id (M i))) of
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.lift_of`：lift_of {N} [Monoid N] (fi : forall i, M i ->* N
) {i} (m : M i) : lift fi (of m) = fi i m
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_leftInverse [DecidableEq ι] (i : ι) :
    Function.LeftInverse (lift <| Pi.mulSingle i (MonoidHom.id (M i))) of := fun x => by
  simp only [lift_of, Pi.mulSingle_eq_same, MonoidHom.id_apply]
/-
**Monoid.CoprodI.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：of_injective (i : ι) : Function.Injective (of : M i ->* _)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Monoid.CoprodI.of_leftInverse`：of_leftInverse [DecidableEq ι] (i : ι) : 
Function.LeftInverse (lift <| Pi.mulSingle i (MonoidHom.id (M i))) of
-/
theorem of_injective (i : ι) : Function.Injective (of : M i →* _) := by
  classical exact (of_leftInverse i).injective

set_option backward.isDefEq.respectTransparency false in
/-
**Monoid.CoprodI.mrange_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：mrange_eq_iSup {N} [Monoid N] (f : forall i, M i ->* N) : MonoidHom.mrange
 (lift f) = ⨆ i, MonoidHom.mrange (f i)
参数：f : forall i, M i ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.lift.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_2} [inst : (i
 : ι) → Monoid (M i)] {N : Type u_3} [inst_1 : Monoid N],   Monoid.CoprodI.lift 
=     { toFun …
· 使用定理 `Equiv.coe_fn_mk`：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l 
: Function.LeftInverse g f) (r : Function.RightInverse g f),   ⇑{ toFun := f, in
vFun …
· 使用定理 `Con.lift_range`：lift_range (H : c <= ker f) : MonoidHom.mrange (c.lift f
 H) = MonoidHom.mrange f
· 使用定理 `FreeMonoid.mrange_lift`：∀ {M : Type u_1} [inst : Monoid M] {α : Type u_4
} (f : α → M),   MonoidHom.mrange (FreeMonoid.lift f) = Submonoid.closure (Set.r
ange f)
· 使用定理 `Set.range_sigma_eq_iUnion_range`：range_sigma_eq_iUnion_range {γ : α -> T
ype*} (f : Sigma γ -> β) : range f = ⋃ a, range fun b => f ⟨a, b⟩
· 使用定理 `Submonoid.closure_iUnion`：closure_iUnion {ι} (s : ι -> Set M) : closure 
(⋃ i, s i) = ⨆ i, closure (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidHom.mclosure_range`：mclosure_range (f : F) : closure (Set.range f)
 = mrange f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mrange_eq_iSup {N} [Monoid N] (f : ∀ i, M i →* N) :
    MonoidHom.mrange (lift f) = ⨆ i, MonoidHom.mrange (f i) := by
  rw [lift, Equiv.coe_fn_mk, Con.lift_range, FreeMonoid.mrange_lift,
    range_sigma_eq_iUnion_range, Submonoid.closure_iUnion]
  simp +instances only [MonoidHom.mclosure_range]
/-
**Monoid.CoprodI.lift_mrange_le** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：lift_mrange_le {N} [Monoid N] (f : forall i, M i ->* N) {s : Submonoid N} 
: MonoidHom.mrange (lift f) <= s ↔ forall i, MonoidHom.mrange (f i) <= s
参数：f : forall i, M i ->* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.mrange_eq_iSup`：mrange_eq_iSup {N} [Monoid N] (f : forall
 i, M i ->* N) : MonoidHom.mrange (lift f) = ⨆ i, MonoidHom.mrange (f i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_mrange_le {N} [Monoid N] (f : ∀ i, M i →* N) {s : Submonoid N} :
    MonoidHom.mrange (lift f) ≤ s ↔ ∀ i, MonoidHom.mrange (f i) ≤ s := by
  simp [mrange_eq_iSup]

@[simp]
/-
**Monoid.CoprodI.iSup_mrange_of** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：iSup_mrange_of : ⨆ i, MonoidHom.mrange (of : M i ->* CoprodI M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mrange.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : Mul
OneClass M] [inst_1 : MulOneClass N] {F : Type u_4} [inst_2 : FunLike F M N]   [
mc : MonoidHomCla…
· 使用定理 `Monoid.CoprodI.lift_of'`：lift_of' : lift (fun i => (of : M i ->* CoprodI
 M)) = .id (CoprodI M)
· 使用定理 `MonoidHom.mrange_id`：mrange_id : mrange (MonoidHom.id M) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_mrange_of : ⨆ i, MonoidHom.mrange (of : M i →* CoprodI M) = ⊤ := by
  simp [← mrange_eq_iSup]

@[simp]
/-
**Monoid.CoprodI.mclosure_iUnion_range_of** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Copr
odI`。
形式化陈述：mclosure_iUnion_range_of : Submonoid.closure (⋃ i, Set.range (of : M i ->*
 CoprodI M)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.closure_iUnion`：closure_iUnion {ι} (s : ι -> Set M) : closure 
(⋃ i, s i) = ⨆ i, closure (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidHom.mclosure_range`：mclosure_range (f : F) : closure (Set.range f)
 = mrange f
· 使用定理 `Monoid.CoprodI.iSup_mrange_of`：iSup_mrange_of : ⨆ i, MonoidHom.mrange (o
f : M i ->* CoprodI M) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mclosure_iUnion_range_of :
    Submonoid.closure (⋃ i, Set.range (of : M i →* CoprodI M)) = ⊤ := by
  simp [Submonoid.closure_iUnion]

@[elab_as_elim]
/-
**Monoid.CoprodI.induction_left** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：induction_left {motive : CoprodI M -> Prop} (m : CoprodI M) (one : motive 
1) (mul : forall {i} (m : M i) x, motive x -> motive (of m * x)) : motive m
参数：m : CoprodI M；one : motive 1；mul : forall {i} (m : M i) x, motive x -> motive
 (of m * x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.induction_of_closure_eq_top_left`：induction_of_closure_eq_top_
left {s : Set M} {motive : M -> Prop} (hs : closure s = ⊤) (x : M) (one : motive
 1) (mul_left : forall x in s, f…
· 使用定理 `Monoid.CoprodI.mclosure_iUnion_range_of`：mclosure_iUnion_range_of : Subm
onoid.closure (⋃ i, Set.range (of : M i ->* CoprodI M)) = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem induction_left {motive : CoprodI M → Prop} (m : CoprodI M) (one : motive 1)
    (mul : ∀ {i} (m : M i) x, motive x → motive (of m * x)) : motive m := by
  induction m using Submonoid.induction_of_closure_eq_top_left mclosure_iUnion_range_of with
  | one => exact one
  | mul_left x hx y ihy =>
    obtain ⟨i, m, rfl⟩ : ∃ (i : ι) (m : M i), of m = x := by simpa using hx
    exact mul m y ihy

@[elab_as_elim]
/-
**Monoid.CoprodI.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：induction_on {motive : CoprodI M -> Prop} (m : CoprodI M) (one : motive 1)
 (of : forall (i) (m : M i), motive (of m)) (mul : forall x y, motive x -> motiv
e y -> motive (x * y)) : motive m
参数：m : CoprodI M；one : motive 1；of : forall (i) (m : M i), motive (of m)；mul : f
orall x y, motive x -> motive y -> motive (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.induction_left`：induction_left {motive : CoprodI M -> Pro
p} (m : CoprodI M) (one : motive 1) (mul : forall {i} (m : M i) x, motive x -> m
otive (of m * x)) :…
-/
theorem induction_on {motive : CoprodI M → Prop} (m : CoprodI M) (one : motive 1)
    (of : ∀ (i) (m : M i), motive (of m))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive m :=
  induction_left m one fun {_} _ _ ↦ mul _ _ (of _ _)

section Group

variable (G : ι → Type*) [∀ i, Group (G i)]

/-
**Monoid.CoprodI.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (CoprodI G) where
  inv :=
    MulOpposite.unop ∘ lift fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom
/-
**Monoid.CoprodI.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：inv_def (x : CoprodI G) : x⁻¹ = MulOpposite.unop (lift (fun i => (of : G i
 ->* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom) x)
参数：x : CoprodI G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (x : CoprodI G) :
    x⁻¹ =
      MulOpposite.unop
        (lift (fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom) x) :=
  rfl
/-
**Monoid.CoprodI.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (CoprodI G) :=
  { inv_mul_cancel := by
      intro m
      rw [inv_def]
      induction m using CoprodI.induction_on with
      | one => rw [map_one, MulOpposite.unop_one, one_mul]
      | of m ih =>
        change of _⁻¹ * of _ = 1
        rw [← of.map_mul, inv_mul_cancel, of.map_one]
      | mul x y ihx ihy =>
        rw [map_mul, MulOpposite.unop_mul, mul_assoc, ← mul_assoc _ x y, ihx, one_mul,
          ihy] }
/-
**Monoid.CoprodI.lift_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：lift_range_le {N} [Group N] (f : forall i, G i ->* N) {s : Subgroup N} (h 
: forall i, (f i).range <= s) : (lift f).range <= s
参数：f : forall i, G i ->* N；h : forall i, (f i).range <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.induction_on`：induction_on {motive : CoprodI M -> Prop} (
m : CoprodI M) (one : motive 1) (of : forall (i) (m : M i), motive (of m)) (mul 
: forall x y, mot…
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.lift_of`：lift_of {N} [Monoid N] (fi : forall i, M i ->* N
) {i} (m : M i) : lift fi (of m) = fi i m
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
-/
theorem lift_range_le {N} [Group N] (f : ∀ i, G i →* N) {s : Subgroup N}
    (h : ∀ i, (f i).range ≤ s) : (lift f).range ≤ s := by
  rintro _ ⟨x, rfl⟩
  induction x using CoprodI.induction_on with
  | one => exact s.one_mem
  | of i x =>
    simp only [lift_of]
    exact h i (Set.mem_range_self x)
  | mul x y hx hy =>
    simp only [map_mul]
    exact s.mul_mem hx hy
/-
**Monoid.CoprodI.range_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：range_eq_iSup {N} [Group N] (f : forall i, G i ->* N) : (lift f).range = ⨆
 i, (f i).range
参数：f : forall i, G i ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Monoid.CoprodI.lift_range_le`：lift_range_le {N} [Group N] (f : forall i,
 G i ->* N) {s : Subgroup N} (h : forall i, (f i).range <= s) : (lift f).range <
= s
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.lift_of`：lift_of {N} [Monoid N] (fi : forall i, M i ->* N
) {i} (m : M i) : lift fi (of m) = fi i m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_eq_iSup {N} [Group N] (f : ∀ i, G i →* N) : (lift f).range = ⨆ i, (f i).range := by
  apply le_antisymm (lift_range_le _ f fun i => le_iSup (fun i => MonoidHom.range (f i)) i)
  apply iSup_le _
  rintro i _ ⟨x, rfl⟩
  exact ⟨of x, by simp only [lift_of]⟩

end Group

namespace Word

/-- The empty reduced word. -/
@[simps]
/-
**Monoid.CoprodI.Word.empty** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：empty : Word M where toList
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty reduced word.
-/
def empty : Word M where
  toList := []
  ne_one := by simp
  chain_ne := List.isChain_nil
/-
**Monoid.CoprodI.Word.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI.Word`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Word M) :=
  ⟨empty⟩

/-- A reduced word determines an element of the free product, given by multiplication. -/
/-
**Monoid.CoprodI.Word.prod** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：prod (w : Word M) : CoprodI M
参数：w : Word M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reduced word determines an element of the free product, given by multiplicatio
n.
-/
def prod (w : Word M) : CoprodI M :=
  List.prod (w.toList.map fun l => of l.snd)

@[simp]
/-
**Monoid.CoprodI.Word.prod_empty** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Word`
。
形式化陈述：prod_empty : prod (empty : Word M) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_empty : prod (empty : Word M) = 1 :=
  rfl

/-- `fstIdx w` is `some i` if the first letter of `w` is `⟨i, m⟩` with `m : M i`. If `w` is empty
then it's `none`. -/
/-
**Monoid.CoprodI.Word.fstIdx** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：fstIdx (w : Word M) : Option ι
参数：w : Word M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fstIdx w` is `some i` if the first letter of `w` is `⟨i, m⟩` with `m : M i`. If
 `w` is empty
then it's `none`.
-/
def fstIdx (w : Word M) : Option ι :=
  w.toList.head?.map Sigma.fst
/-
**Monoid.CoprodI.Word.fstIdx_ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Wo
rd`。
形式化陈述：fstIdx_ne_iff {w : Word M} {i} : fstIdx w != some i ↔ forall l in w.toList
.head?, i != Sigma.fst l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fstIdx_ne_iff {w : Word M} {i} :
    fstIdx w ≠ some i ↔ ∀ l ∈ w.toList.head?, i ≠ Sigma.fst l :=
  not_iff_not.mp <| by simp [fstIdx]

variable (M)

/-- Given an index `i : ι`, `Pair M i` is the type of pairs `(head, tail)` where `head : M i` and
`tail : Word M`, subject to the constraint that first letter of `tail` can't be `⟨i, m⟩`.
By prepending `head` to `tail`, one obtains a new word. We'll show that any word can be uniquely
obtained in this way. -/
@[ext]
/-
**Monoid.CoprodI.Word.Pair** 是 Mathlib 中的一个归纳类型，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：{ι : Type u_1} → (M : ι → Type u_2) → [(i : ι) → Monoid (M i)] → ι → Type 
(max u_1 u_2)
参数：M : ι → Type u_2；i : ι；M i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an index `i : ι`, `Pair M i` is the type of pairs `(head, tail)` where `he
ad : M i` and
`tail : Word M`, subject to the constraint that first letter of `tail` can't be 
`⟨i, m⟩`.
By prepending `head` to `tail`, one obtains a new word. We'll show that any word
 can be uniquely
obtained in this way.
-/
structure Pair (i : ι) where
  /-- An element of `M i`, the first letter of the word. -/
  head : M i
  /-- The remaining letters of the word, excluding the first letter -/
  tail : Word M
  /-- The index first letter of tail of a `Pair M i` is not equal to `i` -/
  fstIdx_ne : fstIdx tail ≠ some i
/-
**Monoid.CoprodI.Word.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI.Word`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : Inhabited (Pair M i) :=
  ⟨⟨1, empty, by tauto⟩⟩

variable {M}

/-- Construct a new `Word` without any reduction. The underlying list of
`cons m w _ _` is `⟨_, m⟩::w` -/
@[simps]
/-
**Monoid.CoprodI.Word.cons** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：cons {i} (m : M i) (w : Word M) (hmw : w.fstIdx != some i) (h1 : m != 1) :
 Word M
参数：m : M i；w : Word M；hmw : w.fstIdx != some i；h1 : m != 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a new `Word` without any reduction. The underlying list of
`cons m w _ _` is `⟨_, m⟩::w`
-/
def cons {i} (m : M i) (w : Word M) (hmw : w.fstIdx ≠ some i) (h1 : m ≠ 1) : Word M :=
  { toList := ⟨i, m⟩ :: w.toList,
    ne_one := by
      simp only [List.mem_cons]
      rintro l (rfl | hl)
      · exact h1
      · exact w.ne_one l hl
    chain_ne := w.chain_ne.cons (fstIdx_ne_iff.mp hmw) }

@[simp]
/-
**Monoid.CoprodI.Word.fstIdx_cons** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Word
`。
形式化陈述：fstIdx_cons {i} (m : M i) (w : Word M) (hmw : w.fstIdx != some i) (h1 : m 
!= 1) : fstIdx (cons m w hmw h1) = some i
参数：m : M i；w : Word M；hmw : w.fstIdx != some i；h1 : m != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fstIdx_cons {i} (m : M i) (w : Word M) (hmw : w.fstIdx ≠ some i) (h1 : m ≠ 1) :
    fstIdx (cons m w hmw h1) = some i := by simp [cons, fstIdx]

@[simp]
/-
**Monoid.CoprodI.Word.prod_cons** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：prod_cons (i) (m : M i) (w : Word M) (h1 : m != 1) (h2 : w.fstIdx != some 
i) : prod (cons m w h2 h1) = of m * prod w
参数：i；m : M i；w : Word M；h1 : m != 1；h2 : w.fstIdx != some i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_cons (i) (m : M i) (w : Word M) (h1 : m ≠ 1) (h2 : w.fstIdx ≠ some i) :
    prod (cons m w h2 h1) = of m * prod w := by
  simp [cons, prod, List.map_cons, List.prod_cons]

section
variable [∀ i, DecidableEq (M i)]

/-- Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, except if `head`
is `1 : M i` then we have to just return `Word` since we need the result to be reduced. -/
/-
**Monoid.CoprodI.Word.rcons** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：rcons {i} (p : Pair M i) : Word M
参数：p : Pair M i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…

--- 原说明 ---
Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, 
except if `head`
is `1 : M i` then we have to just return `Word` since we need the result to be r
educed.
-/
def rcons {i} (p : Pair M i) : Word M :=
  if h : p.head = 1 then p.tail
  else cons p.head p.tail p.fstIdx_ne h

@[simp]
/-
**Monoid.CoprodI.Word.prod_rcons** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Word`
。
形式化陈述：prod_rcons {i} (p : Pair M i) : prod (rcons p) = of p.head * prod p.tail
参数：p : Pair M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.rcons.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_2} [ins
t : (i : ι) → Monoid (M i)] [inst_1 : (i : ι) → DecidableEq (M i)] {i : ι}   (p 
: Monoid.CoprodI.Wor…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Monoid.CoprodI.Word.cons.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_2} [inst
 : (i : ι) → Monoid (M i)] {i : ι} (m : M i) (w : Monoid.CoprodI.Word M)   (hmw 
: w.fstIdx ≠ some i…
· 使用定理 `Monoid.CoprodI.Word.prod.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_2} [inst
 : (i : ι) → Monoid (M i)] (w : Monoid.CoprodI.Word M),   w.prod = (List.map (fu
n l => Monoid.Copro…
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
-/
theorem prod_rcons {i} (p : Pair M i) : prod (rcons p) = of p.head * prod p.tail :=
  if hm : p.head = 1 then by rw [rcons, dif_pos hm, hm, map_one, one_mul]
  else by rw [rcons, dif_neg hm, cons, prod, List.map_cons, List.prod_cons, prod]
/-
**Monoid.CoprodI.Word.rcons_inj** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：rcons_inj {i} : Function.Injective (rcons : Pair M i -> Word M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Monoid.CoprodI.Word.Pair.mk.congr_simp`：∀ {ι : Type u_1} {M : ι → Type u
_2} [inst : (i : ι) → Monoid (M i)] {i : ι} (head head_1 : M i),   head = head_1
 →     ∀ (tail tail_1 : Mono…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.CoprodI.Word.mk.injEq`：∀ {ι : Type u_1} {M : ι → Type u_2} [inst 
: (i : ι) → Monoid (M i)] (toList : List ((i : ι) × M i))   (ne_one : ∀ l ∈ toLi
st, l.snd ≠ 1) (ch…
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Monoid.CoprodI.Word.ext`：∀ {ι : Type u_1} {M : ι → Type u_2} {inst : (i 
: ι) → Monoid (M i)} {x y : Monoid.CoprodI.Word M},   x.toList = y.toList → x = 
y
-/
theorem rcons_inj {i} : Function.Injective (rcons : Pair M i → Word M) := by
  rintro ⟨m, w, h⟩ ⟨m', w', h'⟩ he
  by_cases hm : m = 1 <;> by_cases hm' : m' = 1
  · simp only [rcons, dif_pos hm, dif_pos hm'] at he
    simp_all
  · exfalso
    simp only [rcons, dif_pos hm, dif_neg hm'] at he
    rw [he] at h
    exact h rfl
  · exfalso
    simp only [rcons, dif_pos hm', dif_neg hm] at he
    rw [← he] at h'
    exact h' rfl
  · have : m = m' ∧ w.toList = w'.toList := by
      simpa [cons, rcons, dif_neg hm, dif_neg hm', eq_self_iff_true, Subtype.mk_eq_mk,
        heq_iff_eq, ← Subtype.ext_iff] using he
    rcases this with ⟨rfl, h⟩
    congr
    exact Word.ext h
/-
**Monoid.CoprodI.Word.mem_rcons_iff** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Wo
rd`。
形式化陈述：mem_rcons_iff {i j : ι} (p : Pair M i) (m : M j) : ⟨_, m⟩ in (rcons p).toL
ist ↔ ⟨_, m⟩ in p.tail.toList ∨ m != 1 ∧ (exists h : i = j, m = h ▸ p.head)
参数：p : Pair M i；m : M j。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_rcons_iff {i j : ι} (p : Pair M i) (m : M j) :
    ⟨_, m⟩ ∈ (rcons p).toList ↔ ⟨_, m⟩ ∈ p.tail.toList ∨
      m ≠ 1 ∧ (∃ h : i = j, m = h ▸ p.head) := by
  simp only [rcons, cons, ne_eq]
  grind

end

/-- Induct on a word by adding letters one at a time without reduction,
effectively inducting on the underlying `List`. -/
@[elab_as_elim]
/-
**Monoid.CoprodI.Word.consRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：consRecOn {motive : Word M -> Sort*} (w : Word M) (empty : motive empty) (
cons : forall (i) (m : M i) (w) h1 h2, motive w -> motive (cons m w h1 h2)) : mo
tive w
参数：w : Word M；empty : motive empty；cons : forall (i) (m : M i) (w) h1 h2, motive
 w -> motive (cons m w h1 h2)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induct on a word by adding letters one at a time without reduction,
effectively inducting on the underlying `List`.
-/
def consRecOn {motive : Word M → Sort*} (w : Word M) (empty : motive empty)
    (cons : ∀ (i) (m : M i) (w) h1 h2, motive w → motive (cons m w h1 h2)) :
    motive w := by
  rcases w with ⟨w, h1, h2⟩
  induction w with
  | nil => exact empty
  | cons m w ih =>
    refine cons m.1 m.2 ⟨w, fun _ hl => h1 _ (List.mem_cons_of_mem _ hl), h2.tail⟩ ?_ ?_ (ih _ _)
    · rw [List.isChain_cons] at h2
      simp only [fstIdx, ne_eq, Option.map_eq_some_iff,
        Sigma.exists, exists_and_right, exists_eq_right, not_exists]
      intro m' hm'
      exact h2.1 _ hm' rfl
    · exact h1 _ List.mem_cons_self

@[simp]
/-
**Monoid.CoprodI.Word.consRecOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.
Word`。
形式化陈述：consRecOn_empty {motive : Word M -> Sort*} (h_empty : motive empty) (h_con
s : forall (i) (m : M i) (w) h1 h2, motive w -> motive (cons m w h1 h2)) : consR
ecOn empty h_empty h_cons = h_empty
参数：h_empty : motive empty；h_cons : forall (i) (m : M i) (w) h1 h2, motive w -> m
otive (cons m w h1 h2)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem consRecOn_empty {motive : Word M → Sort*} (h_empty : motive empty)
    (h_cons : ∀ (i) (m : M i) (w) h1 h2, motive w → motive (cons m w h1 h2)) :
    consRecOn empty h_empty h_cons = h_empty := rfl

@[simp]
/-
**Monoid.CoprodI.Word.consRecOn_cons** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.W
ord`。
形式化陈述：consRecOn_cons {motive : Word M -> Sort*} (i) (m : M i) (w : Word M) h1 h2
 (h_empty : motive empty) (h_cons : forall (i) (m : M i) (w) h1 h2, motive w -> 
motive (cons m w h1 h2)) : consRecOn (cons m w h1 h2) h_empty h_cons = h_cons i 
m w h1 h2 (consRecOn w h_empty h_cons)
参数：i；m : M i；w : Word M；h_empty : motive empty；h_cons : forall (i) (m : M i) (w)
 h1 h2, motive w -> motive (cons m w h1 h2)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem consRecOn_cons {motive : Word M → Sort*} (i) (m : M i) (w : Word M) h1 h2
    (h_empty : motive empty)
    (h_cons : ∀ (i) (m : M i) (w) h1 h2, motive w → motive (cons m w h1 h2)) :
    consRecOn (cons m w h1 h2) h_empty h_cons = h_cons i m w h1 h2
      (consRecOn w h_empty h_cons) := rfl

variable [DecidableEq ι] [∀ i, DecidableEq (M i)]

set_option backward.privateInPublic true in
-- This definition is computable but not very nice to look at. Thankfully we don't have to inspect
-- it, since `rcons` is known to be injective.
/-- Given `i : ι`, any reduced word can be decomposed into a pair `p` such that `w = rcons p`. -/
/-
**Monoid.CoprodI.Word.equivPairAux** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Wor
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `i : ι`, any reduced word can be decomposed into a pair `p` such that `w =
 rcons p`.
-/
private def equivPairAux (i) (w : Word M) : { p : Pair M i // rcons p = w } :=
  consRecOn w ⟨⟨1, .empty, by simp [fstIdx, empty]⟩, by simp [rcons]⟩ <|
    fun j m w h1 h2 _ =>
      if ij : i = j then
        { val :=
          { head := ij ▸ m
            tail := w
            fstIdx_ne := ij ▸ h1 }
          property := by subst ij; simp [rcons, h2] }
      else ⟨⟨1, cons m w h1 h2, by simp [cons, fstIdx, Ne.symm ij]⟩, by simp [rcons]⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The equivalence between words and pairs. Given a word, it decomposes it as a pair by removing
the first letter if it comes from `M i`. Given a pair, it prepends the head to the tail. -/
/-
**Monoid.CoprodI.Word.equivPair** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：equivPair (i) : Word M ≃ Pair M i where toFun w
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between words and pairs. Given a word, it decomposes it as a pai
r by removing
the first letter if it comes from `M i`. Given a pair, it prepends the head to t
he tail.
-/
def equivPair (i) : Word M ≃ Pair M i where
  toFun w := (equivPairAux i w).val
  invFun := rcons
  left_inv w := (equivPairAux i w).property
  right_inv _ := rcons_inj (equivPairAux i _).property
/-
**Monoid.CoprodI.Word.equivPair_symm** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.W
ord`。
形式化陈述：equivPair_symm (i) (p : Pair M i) : (equivPair i).symm p = rcons p
参数：i；p : Pair M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivPair_symm (i) (p : Pair M i) : (equivPair i).symm p = rcons p :=
  rfl
/-
**Monoid.CoprodI.Word.equivPair_eq_of_fstIdx_ne** 是 Mathlib 中的一个定理，位于命名空间 `Monoi
d.CoprodI.Word`。
形式化陈述：equivPair_eq_of_fstIdx_ne {i} {w : Word M} (h : fstIdx w != some i) : equi
vPair i w = ⟨1, w, h⟩
参数：h : fstIdx w != some i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
-/
theorem equivPair_eq_of_fstIdx_ne {i} {w : Word M} (h : fstIdx w ≠ some i) :
    equivPair i w = ⟨1, w, h⟩ :=
  (equivPair i).eq_symm_apply.mp <| Eq.symm (dif_pos rfl)
/-
**Monoid.CoprodI.Word.mem_equivPair_tail_iff** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.C
oprodI.Word`。
形式化陈述：mem_equivPair_tail_iff {i j : ι} {w : Word M} (m : M i) : (⟨i, m⟩ in (equi
vPair j w).tail.toList) ↔ ⟨i, m⟩ in w.toList.tail ∨ i != j ∧ exists h : w.toList
 != [], w.toList.head h = ⟨i, m⟩
参数：m : M i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Monoid.CoprodI.Word.empty_toList`：∀ {ι : Type u_1} {M : ι → Type u_2} [i
nst : (i : ι) → Monoid (M i)], Monoid.CoprodI.Word.empty.toList = []
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `List.head.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = as_
1) (a : as ≠ []), as.head a = as_1.head ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Monoid.CoprodI.Word.cons_toList`：∀ {ι : Type u_1} {M : ι → Type u_2} [in
st : (i : ι) → Monoid (M i)] {i : ι} (m : M i) (w : Monoid.CoprodI.Word M)   (hm
w : w.fstIdx ≠ some i…
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
（共 34 条，此处仅展示前 30 条）
-/
theorem mem_equivPair_tail_iff {i j : ι} {w : Word M} (m : M i) :
    (⟨i, m⟩ ∈ (equivPair j w).tail.toList) ↔ ⟨i, m⟩ ∈ w.toList.tail
      ∨ i ≠ j ∧ ∃ h : w.toList ≠ [], w.toList.head h = ⟨i, m⟩ := by
  simp only [equivPair, equivPairAux, ne_eq, Equiv.coe_fn_mk]
  induction w using consRecOn with
  | empty => simp
  | cons k g tail h1 h2 ih =>
    simp only [consRecOn_cons]
    split_ifs with h
    · subst k
      by_cases hij : j = i <;> simp_all
    · by_cases hik : i = k
      · subst i; simp_all [@eq_comm _ m g, @eq_comm _ k j, or_comm]
      · simp [hik, Ne.symm hik]
/-
**Monoid.CoprodI.Word.mem_of_mem_equivPair_tail** 是 Mathlib 中的一个定理，位于命名空间 `Monoi
d.CoprodI.Word`。
形式化陈述：mem_of_mem_equivPair_tail {i j : ι} {w : Word M} (m : M i) : (⟨i, m⟩ in (e
quivPair j w).tail.toList) -> ⟨i, m⟩ in w.toList
参数：m : M i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.mem_equivPair_tail_iff`：mem_equivPair_tail_iff {i j 
: ι} {w : Word M} (m : M i) : (⟨i, m⟩ in (equivPair j w).tail.toList) ↔ ⟨i, m⟩ i
n w.toList.tail ∨ i != j ∧ exist…
· 使用定理 `List.mem_of_mem_tail`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l.tail 
→ a ∈ l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem mem_of_mem_equivPair_tail {i j : ι} {w : Word M} (m : M i) :
    (⟨i, m⟩ ∈ (equivPair j w).tail.toList) → ⟨i, m⟩ ∈ w.toList := by
  rw [mem_equivPair_tail_iff]
  rintro (h | h)
  · exact List.mem_of_mem_tail h
  · revert h; cases w.toList <;> simp +contextual

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Monoid.CoprodI.Word.equivPair_head** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.W
ord`。
形式化陈述：equivPair_head {i : ι} {w : Word M} : (equivPair i w).head = if h : exists
 (h : w.toList != []), (w.toList.head h).1 = i then h.snd ▸ (w.toList.head h.1).
2 else 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem equivPair_head {i : ι} {w : Word M} :
    (equivPair i w).head =
      if h : ∃ (h : w.toList ≠ []), (w.toList.head h).1 = i
      then h.snd ▸ (w.toList.head h.1).2
      else 1 := by
  simp only [equivPair, equivPairAux]
  induction w using consRecOn with
  | empty => simp
  | cons head =>
    by_cases hi : i = head
    · subst hi; simp
    · simp [hi, Ne.symm hi]
/-
**Monoid.CoprodI.Word.summandAction** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI.Wo
rd`。
形式化陈述：summandAction (i) : MulAction (M i) (Word M) where smul m w
参数：i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
-/
instance summandAction (i) : MulAction (M i) (Word M) where
  smul m w := rcons { equivPair i w with head := m * (equivPair i w).head }
  one_smul w := by
    apply (equivPair i).symm_apply_eq.mpr
    simp [equivPair]
  mul_smul m m' w := by
    dsimp +instances [instHSMul]
    simp [mul_assoc, ← equivPair_symm, Equiv.apply_symm_apply]
/-
**Monoid.CoprodI.Word.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI.Word`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (CoprodI M) (Word M) :=
  MulAction.ofEndHom (lift fun _ => MulAction.toEndHom)
/-
**Monoid.CoprodI.Word.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：smul_def {i} (m : M i) (w : Word M) : m • w = rcons { equivPair i w with h
ead
参数：m : M i；w : Word M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def {i} (m : M i) (w : Word M) :
    m • w = rcons { equivPair i w with head := m * (equivPair i w).head } :=
  rfl
/-
**Monoid.CoprodI.Word.of_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Word
`。
形式化陈述：of_smul_def (i) (w : Word M) (m : M i) : of m • w = rcons { equivPair i w 
with head
参数：i；w : Word M；m : M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_smul_def (i) (w : Word M) (m : M i) :
    of m • w = rcons { equivPair i w with head := m * (equivPair i w).head } :=
  rfl
/-
**Monoid.CoprodI.Word.equivPair_smul_same** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Copr
odI.Word`。
形式化陈述：equivPair_smul_same {i} (m : M i) (w : Word M) : equivPair i (of m • w) = 
⟨m * (equivPair i w).head, (equivPair i w).tail, (equivPair i w).fstIdx_ne⟩
参数：m : M i；w : Word M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.of_smul_def`：of_smul_def (i) (w : Word M) (m : M i) 
: of m • w = rcons { equivPair i w with head
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.CoprodI.Word.equivPair_symm`：equivPair_symm (i) (p : Pair M i) : 
(equivPair i).symm p = rcons p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivPair_smul_same {i} (m : M i) (w : Word M) :
    equivPair i (of m • w) = ⟨m * (equivPair i w).head, (equivPair i w).tail,
      (equivPair i w).fstIdx_ne⟩ := by
  rw [of_smul_def, ← equivPair_symm]
  simp

@[simp]
/-
**Monoid.CoprodI.Word.equivPair_tail** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.W
ord`。
形式化陈述：equivPair_tail {i} (p : Pair M i) : equivPair i p.tail = ⟨1, p.tail, p.fst
Idx_ne⟩
参数：p : Pair M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.Word.equivPair_eq_of_fstIdx_ne`：equivPair_eq_of_fstIdx_ne
 {i} {w : Word M} (h : fstIdx w != some i) : equivPair i w = ⟨1, w, h⟩
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
-/
theorem equivPair_tail {i} (p : Pair M i) :
    equivPair i p.tail = ⟨1, p.tail, p.fstIdx_ne⟩ :=
  equivPair_eq_of_fstIdx_ne _
/-
**Monoid.CoprodI.Word.smul_eq_of_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.
Word`。
形式化陈述：smul_eq_of_smul {i} (m : M i) (w : Word M) : m • w = of m • w
参数：m : M i；w : Word M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_eq_of_smul {i} (m : M i) (w : Word M) :
    m • w = of m • w := rfl
/-
**Monoid.CoprodI.Word.mem_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Wor
d`。
形式化陈述：mem_smul_iff {i j : ι} {m₁ : M i} {m₂ : M j} {w : Word M} : ⟨_, m₁⟩ in (of
 m₂ • w).toList ↔ (¬i = j ∧ ⟨i, m₁⟩ in w.toList) ∨ (m₁ != 1 ∧ exists (hij : i = 
j), (⟨i, m₁⟩ in w.toList.tail) ∨ (exists m', ⟨j, m'⟩ in w.toList.head? ∧ m₁ = hi
j ▸ (m₂ * m')) ∨ (w.fstIdx != some j ∧ m₁ = hij ▸ m₂))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.of_smul_def`：of_smul_def (i) (w : Word M) (m : M i) 
: of m • w = rcons { equivPair i w with head
· 使用定理 `Monoid.CoprodI.Word.mem_rcons_iff`：mem_rcons_iff {i j : ι} (p : Pair M i
) (m : M j) : ⟨_, m⟩ in (rcons p).toList ↔ ⟨_, m⟩ in p.tail.toList ∨ m != 1 ∧ (e
xists h : i = j, m = h …
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Monoid.CoprodI.Word.mem_equivPair_tail_iff`：mem_equivPair_tail_iff {i j 
: ι} {w : Word M} (m : M i) : (⟨i, m⟩ in (equivPair j w).tail.toList) ↔ ⟨i, m⟩ i
n w.toList.tail ∨ i != j ∧ exist…
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
· 使用定理 `Monoid.CoprodI.Word.equivPair_head`：equivPair_head {i : ι} {w : Word M} 
: (equivPair i w).head = if h : exists (h : w.toList != []), (w.toList.head h).1
 = i then h.snd ▸ (w.toL…
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Monoid.CoprodI.Word.ne_one`：∀ {ι : Type u_1} {M : ι → Type u_2} [inst : 
(i : ι) → Monoid (M i)] (self : Monoid.CoprodI.Word M),   ∀ l ∈ self.toList, l.s
nd ≠ 1
· 使用定理 `List.mem_of_mem_tail`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l.tail 
→ a ∈ l
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `mul_dite`：mul_dite (a : α) (b : P -> α) (c : ¬P -> α) : (a * if h : P th
en b h else c h) = if h : P then a * b h else a * c h
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
（共 56 条，此处仅展示前 30 条）
-/
theorem mem_smul_iff {i j : ι} {m₁ : M i} {m₂ : M j} {w : Word M} :
    ⟨_, m₁⟩ ∈ (of m₂ • w).toList ↔
      (¬i = j ∧ ⟨i, m₁⟩ ∈ w.toList)
      ∨ (m₁ ≠ 1 ∧ ∃ (hij : i = j), (⟨i, m₁⟩ ∈ w.toList.tail) ∨
        (∃ m', ⟨j, m'⟩ ∈ w.toList.head? ∧ m₁ = hij ▸ (m₂ * m')) ∨
        (w.fstIdx ≠ some j ∧ m₁ = hij ▸ m₂)) := by
  rw [of_smul_def, mem_rcons_iff, mem_equivPair_tail_iff, equivPair_head, or_assoc]
  by_cases hij : i = j
  · subst i
    simp only [not_true, ne_eq, false_and, exists_prop, true_and, false_or]
    by_cases hw : ⟨j, m₁⟩ ∈ w.toList.tail
    · simp [hw, show m₁ ≠ 1 from w.ne_one _ (List.mem_of_mem_tail hw)]
    · simp only [hw, false_or, Option.mem_def, and_congr_right_iff]
      intro hm1
      split_ifs with h
      · rcases h with ⟨hnil, rfl⟩
        simp only [List.head?_eq_some_head hnil, Option.some.injEq]
        constructor
        · rintro rfl
          exact Or.inl ⟨_, rfl, rfl⟩
        · rintro (⟨_, h, rfl⟩ | hm')
          · simp only [Sigma.ext_iff, heq_eq_eq, true_and] at h
            subst h
            rfl
          · simp only [fstIdx, Option.map_eq_some_iff, Sigma.exists,
              exists_and_right, exists_eq_right, not_exists] at hm'
            exact (hm'.1 (w.toList.head hnil).2 (by rw [List.head?_eq_some_head])).elim
      · revert h
        rw [fstIdx]
        cases w.toList
        · simp
        · simp +contextual [Sigma.ext_iff]
  · rcases w with ⟨_ | _, _, _⟩ <;>
    simp [or_comm, hij, Ne.symm hij, eq_comm]
/-
**Monoid.CoprodI.Word.mem_smul_iff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Copro
dI.Word`。
形式化陈述：mem_smul_iff_of_ne {i j : ι} (hij : i != j) {m₁ : M i} {m₂ : M j} {w : Wor
d M} : ⟨_, m₁⟩ in (of m₂ • w).toList ↔ ⟨i, m₁⟩ in w.toList
参数：hij : i != j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_smul_iff_of_ne {i j : ι} (hij : i ≠ j) {m₁ : M i} {m₂ : M j} {w : Word M} :
    ⟨_, m₁⟩ ∈ (of m₂ • w).toList ↔ ⟨i, m₁⟩ ∈ w.toList := by
  simp [mem_smul_iff, *]
/-
**Monoid.CoprodI.Word.cons_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Wor
d`。
形式化陈述：cons_eq_smul {i} {m : M i} {ls h1 h2} : cons m ls h1 h2 = of m • ls
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.of_smul_def`：of_smul_def (i) (w : Word M) (m : M i) 
: of m • w = rcons { equivPair i w with head
· 使用定理 `Monoid.CoprodI.Word.equivPair_eq_of_fstIdx_ne`：equivPair_eq_of_fstIdx_ne
 {i} {w : Word M} (h : fstIdx w != some i) : equivPair i w = ⟨1, w, h⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Monoid.CoprodI.Word.mk.congr_simp`：∀ {ι : Type u_1} {M : ι → Type u_2} [
inst : (i : ι) → Monoid (M i)] (toList toList_1 : List ((i : ι) × M i))   (e_toL
ist : toList = toList_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_eq_smul {i} {m : M i} {ls h1 h2} :
    cons m ls h1 h2 = of m • ls := by
  rw [of_smul_def, equivPair_eq_of_fstIdx_ne _]
  · simp [cons, rcons, h2]
  · exact h1
/-
**Monoid.CoprodI.Word.rcons_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Wo
rd`。
形式化陈述：rcons_eq_smul {i} (p : Pair M i) : rcons p = of p.head • p.tail
参数：p : Pair M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.equivPair_tail`：equivPair_tail {i} (p : Pair M i) : 
equivPair i p.tail = ⟨1, p.tail, p.fstIdx_ne⟩
· 使用定理 `Monoid.CoprodI.Word.Pair.mk.congr_simp`：∀ {ι : Type u_1} {M : ι → Type u
_2} [inst : (i : ι) → Monoid (M i)] {i : ι} (head head_1 : M i),   head = head_1
 →     ∀ (tail tail_1 : Mono…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rcons_eq_smul {i} (p : Pair M i) :
    rcons p = of p.head • p.tail := by
  simp [of_smul_def]

@[simp]
/-
**Monoid.CoprodI.Word.equivPair_head_smul_equivPair_tail** 是 Mathlib 中的一个定理，位于命名
空间 `Monoid.CoprodI.Word`。
形式化陈述：equivPair_head_smul_equivPair_tail {i : ι} (w : Word M) : of (equivPair i 
w).head • (equivPair i w).tail = w
参数：w : Word M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.CoprodI.Word.rcons_eq_smul`：rcons_eq_smul {i} (p : Pair M i) : rc
ons p = of p.head • p.tail
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Monoid.CoprodI.Word.equivPair_symm`：equivPair_symm (i) (p : Pair M i) : 
(equivPair i).symm p = rcons p
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem equivPair_head_smul_equivPair_tail {i : ι} (w : Word M) :
    of (equivPair i w).head • (equivPair i w).tail = w := by
  rw [← rcons_eq_smul, ← equivPair_symm, Equiv.symm_apply_apply]
/-
**Monoid.CoprodI.Word.equivPair_tail_eq_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mono
id.CoprodI.Word`。
形式化陈述：equivPair_tail_eq_inv_smul {G : ι -> Type*} [forall i, Group (G i)] [foral
l i, DecidableEq (G i)] {i} (w : Word G) : (equivPair i w).tail = (of (equivPair
 i w).head)⁻¹ • w
参数：G i；G i；w : Word G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `Monoid.CoprodI.Word.equivPair_head_smul_equivPair_tail`：equivPair_head_s
mul_equivPair_tail {i : ι} (w : Word M) : of (equivPair i w).head • (equivPair i
 w).tail = w
-/
theorem equivPair_tail_eq_inv_smul {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, DecidableEq (G i)] {i} (w : Word G) :
    (equivPair i w).tail = (of (equivPair i w).head)⁻¹ • w :=
  Eq.symm <| inv_smul_eq_iff.2 (equivPair_head_smul_equivPair_tail w).symm

@[elab_as_elim]
/-
**Monoid.CoprodI.Word.smul_induction** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.W
ord`。
形式化陈述：smul_induction {motive : Word M -> Prop} (empty : motive empty) (smul : fo
rall (i) (m : M i) (w), motive w -> motive (of m • w)) (w : Word M) : motive w
参数：empty : motive empty；smul : forall (i) (m : M i) (w), motive w -> motive (of 
m • w)；w : Word M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.cons_eq_smul`：cons_eq_smul {i} {m : M i} {ls h1 h2} 
: cons m ls h1 h2 = of m • ls
-/
theorem smul_induction {motive : Word M → Prop} (empty : motive empty)
    (smul : ∀ (i) (m : M i) (w), motive w → motive (of m • w)) (w : Word M) : motive w := by
  induction w using consRecOn with
  | empty => exact empty
  | cons _ _ _ _ _ ih =>
    rw [cons_eq_smul]
    exact smul _ _ _ ih

@[simp]
/-
**Monoid.CoprodI.Word.prod_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：prod_smul (m) : forall w : Word M, prod (m • w) = m * prod w
参数：m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.CoprodI.induction_on`：induction_on {motive : CoprodI M -> Prop} (
m : CoprodI M) (one : motive 1) (of : forall (i) (m : M i), motive (of m)) (mul 
: forall x y, mot…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `Monoid.CoprodI.Word.of_smul_def`：of_smul_def (i) (w : Word M) (m : M i) 
: of m • w = rcons { equivPair i w with head
· 使用定理 `Monoid.CoprodI.Word.prod_rcons`：prod_rcons {i} (p : Pair M i) : prod (rc
ons p) = of p.head * prod p.tail
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Monoid.CoprodI.Word.equivPair_symm`：equivPair_symm (i) (p : Pair M i) : 
(equivPair i).symm p = rcons p
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem prod_smul (m) : ∀ w : Word M, prod (m • w) = m * prod w := by
  induction m using CoprodI.induction_on with
  | one =>
    intro
    rw [one_smul, one_mul]
  | of _ =>
    intros
    rw [of_smul_def, prod_rcons, of.map_mul, mul_assoc, ← prod_rcons, ← equivPair_symm,
      Equiv.symm_apply_apply]
  | mul x y hx hy =>
    intro w
    rw [mul_smul, hx, hy, mul_assoc]

/-- Each element of the free product corresponds to a unique reduced word. -/
/-
**Monoid.CoprodI.Word.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Word`。
形式化陈述：equiv : CoprodI M ≃ Word M where toFun m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the free product corresponds to a unique reduced word.
-/
def equiv : CoprodI M ≃ Word M where
  toFun m := m • empty
  invFun w := prod w
  left_inv m := by dsimp only; rw [prod_smul, prod_empty, mul_one]
  right_inv := by
    apply smul_induction
    · dsimp only
      rw [prod_empty, one_smul]
    · dsimp only
      intro i m w ih
      rw [prod_smul, mul_smul, ih]
/-
**Monoid.CoprodI.Word.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI.Word`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableEq (Word M) :=
  Function.Injective.decidableEq fun _ _ => Word.ext
/-
**Monoid.CoprodI.Word.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI.Word`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableEq (CoprodI M) :=
  Equiv.decidableEq Word.equiv

end Word

variable (M) in
/-- A `NeWord M i j` is a representation of a non-empty reduced words where the first letter comes
from `M i` and the last letter comes from `M j`. It can be constructed from singletons and via
concatenation, and thus provides a useful induction principle. -/
/-
**Monoid.CoprodI.NeWord** 是 Mathlib 中的一个归纳类型，位于命名空间 `Monoid.CoprodI`。
形式化陈述：{ι : Type u_1} → (M : ι → Type u_2) → [(i : ι) → Monoid (M i)] → ι → ι → T
ype (max u_1 u_2)
参数：M : ι → Type u_2；i : ι；M i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NeWord M i j` is a representation of a non-empty reduced words where the firs
t letter comes
from `M i` and the last letter comes from `M j`. It can be constructed from sing
letons and via
concatenation, and thus provides a useful induction principle.
-/
inductive NeWord : ι → ι → Type _
  | singleton : ∀ {i : ι} (x : M i), x ≠ 1 → NeWord i i
  | append : ∀ {i j k l} (_w₁ : NeWord i j) (_hne : j ≠ k) (_w₂ : NeWord k l), NeWord i l

namespace NeWord

open Word

/-- The list represented by a given `NeWord` -/
@[simp]
/-
**Monoid.CoprodI.NeWord.toList** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.NeWord`
。
形式化陈述：{ι : Type u_1} →   {M : ι → Type u_2} → [inst : (i : ι) → Monoid (M i)] → 
{i j : ι} → Monoid.CoprodI.NeWord M i j → List ((i : ι) × M i)
参数：i : ι；M i；(i : ι) × M i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The list represented by a given `NeWord`
-/
def toList : ∀ {i j} (_w : NeWord M i j), List (Σ i, M i)
  | i, _, singleton x _ => [⟨i, x⟩]
  | _, _, append w₁ _ w₂ => w₁.toList ++ w₂.toList
/-
**Monoid.CoprodI.NeWord.toList_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.
NeWord`。
形式化陈述：toList_ne_nil {i j} (w : NeWord M i j) : w.toList != List.nil
参数：w : NeWord M i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `List.append_ne_nil_of_left_ne_nil`：∀ {α : Type u_1} {s : List α}, s ≠ []
 → ∀ (t : List α), s ++ t ≠ []
-/
theorem toList_ne_nil {i j} (w : NeWord M i j) : w.toList ≠ List.nil := by
  induction w
  · rintro ⟨rfl⟩
  · apply List.append_ne_nil_of_left_ne_nil
    assumption

/-- The first letter of a `NeWord` -/
@[simp]
/-
**Monoid.CoprodI.NeWord.head** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.NeWord`。
形式化陈述：{ι : Type u_1} → {M : ι → Type u_2} → [inst : (i : ι) → Monoid (M i)] → {i
 j : ι} → Monoid.CoprodI.NeWord M i j → M i
参数：i : ι；M i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first letter of a `NeWord`
-/
def head : ∀ {i j} (_w : NeWord M i j), M i
  | _, _, singleton x _ => x
  | _, _, append w₁ _ _ => w₁.head

/-- The last letter of a `NeWord` -/
@[simp]
/-
**Monoid.CoprodI.NeWord.last** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.NeWord`。
形式化陈述：{ι : Type u_1} → {M : ι → Type u_2} → [inst : (i : ι) → Monoid (M i)] → {i
 j : ι} → Monoid.CoprodI.NeWord M i j → M j
参数：i : ι；M i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The last letter of a `NeWord`
-/
def last : ∀ {i j} (_w : NeWord M i j), M j
  | _, _, singleton x _hne1 => x
  | _, _, append _w₁ _hne w₂ => w₂.last

@[simp]
/-
**Monoid.CoprodI.NeWord.toList_head** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Ne
Word`。
形式化陈述：toList_head? {i j} (w : NeWord M i j) : w.toList.head? = Option.some ⟨i, w
.head⟩
参数：w : NeWord M i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toList_head? {i j} (w : NeWord M i j) : w.toList.head? = Option.some ⟨i, w.head⟩ := by
  fun_induction toList with grind [head]

@[simp]
/-
**Monoid.CoprodI.NeWord.toList_getLast** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI
.NeWord`。
形式化陈述：toList_getLast? {i j} (w : NeWord M i j) : w.toList.getLast? = Option.some
 ⟨j, w.last⟩
参数：w : NeWord M i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toList_getLast? {i j} (w : NeWord M i j) : w.toList.getLast? = Option.some ⟨j, w.last⟩ := by
  rw [← Option.mem_def]
  induction w
  · rw [Option.mem_def]
    rfl
  · exact List.mem_getLast?_append_of_mem_getLast? (by assumption)

/-- The `Word M` represented by a `NeWord M i j` -/
/-
**Monoid.CoprodI.NeWord.toWord** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.NeWord`
。
形式化陈述：toWord {i j} (w : NeWord M i j) : Word M where toList
参数：w : NeWord M i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Word M` represented by a `NeWord M i j`
-/
def toWord {i j} (w : NeWord M i j) : Word M where
  toList := w.toList
  ne_one := by
    induction w
    · simpa only [toList, List.mem_singleton, ne_eq, forall_eq]
    · intro l h
      simp only [toList, List.mem_append] at h
      cases h <;> aesop
  chain_ne := by
    induction w
    · exact List.isChain_singleton _
    · refine List.IsChain.append (by assumption) (by assumption) ?_
      intro x hx y hy
      rw [toList_getLast?, Option.mem_some_iff] at hx
      rw [toList_head?, Option.mem_some_iff] at hy
      subst hx
      subst hy
      assumption

/-- Every nonempty `Word M` can be constructed as a `NeWord M i j` -/
/-
**Monoid.CoprodI.NeWord.of_word** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.NeWord
`。
形式化陈述：of_word (w : Word M) (h : w != empty) : exists (i j : _) (w' : NeWord M i 
j), w'.toWord = w
参数：w : Word M；h : w != empty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `Monoid.CoprodI.Word.mk.congr_simp`：∀ {ι : Type u_1} {M : ι → Type u_2} [
inst : (i : ι) → Monoid (M i)] (toList toList_1 : List ((i : ι) × M i))   (e_toL
ist : toList = toList_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Monoid.CoprodI.NeWord.toList_head?`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i j : ι} (w : Monoid.CoprodI.NeWord M i j),   w
.toList.head? = some ⟨i,…
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
· 使用定理 `Monoid.CoprodI.Word.ext`：∀ {ι : Type u_1} {M : ι → Type u_2} {inst : (i 
: ι) → Monoid (M i)} {x y : Monoid.CoprodI.Word M},   x.toList = y.toList → x = 
y
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Every nonempty `Word M` can be constructed as a `NeWord M i j`
-/
theorem of_word (w : Word M) (h : w ≠ empty) : ∃ (i j : _) (w' : NeWord M i j), w'.toWord = w := by
  suffices ∃ (i j : _) (w' : NeWord M i j), w'.toWord.toList = w.toList by
    rcases this with ⟨i, j, w, h⟩
    refine ⟨i, j, w, ?_⟩
    ext
    rw [h]
  obtain ⟨l, hnot1, hchain⟩ := w
  induction l with
  | nil => contradiction
  | cons x l hi =>
    rw [List.forall_mem_cons] at hnot1
    rcases l with - | ⟨y, l⟩
    · refine ⟨x.1, x.1, singleton x.2 hnot1.1, ?_⟩
      simp [toWord]
    · rw [List.isChain_cons_cons] at hchain
      specialize hi hnot1.2 hchain.2 (by rintro ⟨rfl⟩)
      obtain ⟨i, j, w', hw' : w'.toList = y::l⟩ := hi
      obtain rfl : y = ⟨i, w'.head⟩ := by simpa [hw'] using w'.toList_head?
      refine ⟨x.1, j, append (singleton x.2 hnot1.1) hchain.1 w', ?_⟩
      simpa [toWord] using hw'

/-- A non-empty reduced word determines an element of the free product, given by multiplication. -/
/-
**Monoid.CoprodI.NeWord.prod** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.NeWord`。
形式化陈述：prod {i j} (w : NeWord M i j)
参数：w : NeWord M i j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-empty reduced word determines an element of the free product, given by mul
tiplication.
-/
def prod {i j} (w : NeWord M i j) :=
  w.toWord.prod

@[simp]
/-
**Monoid.CoprodI.NeWord.singleton_head** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI
.NeWord`。
形式化陈述：singleton_head {i} (x : M i) (hne_one : x != 1) : (singleton x hne_one).he
ad = x
参数：x : M i；hne_one : x != 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_head {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).head = x :=
  rfl

@[simp]
/-
**Monoid.CoprodI.NeWord.singleton_last** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI
.NeWord`。
形式化陈述：singleton_last {i} (x : M i) (hne_one : x != 1) : (singleton x hne_one).la
st = x
参数：x : M i；hne_one : x != 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_last {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).last = x :=
  rfl

@[simp]
/-
**Monoid.CoprodI.NeWord.prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI
.NeWord`。
形式化陈述：prod_singleton {i} (x : M i) (hne_one : x != 1) : (singleton x hne_one).pr
od = of x
参数：x : M i；hne_one : x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_singleton {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).prod = of x := by
  simp [toWord, prod, Word.prod]

@[simp]
/-
**Monoid.CoprodI.NeWord.append_head** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Ne
Word`。
形式化陈述：append_head {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k 
l} : (append w₁ hne w₂).head = w₁.head
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_head {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).head = w₁.head :=
  rfl

@[simp]
/-
**Monoid.CoprodI.NeWord.append_last** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Ne
Word`。
形式化陈述：append_last {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k 
l} : (append w₁ hne w₂).last = w₂.last
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_last {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).last = w₂.last :=
  rfl

@[simp]
/-
**Monoid.CoprodI.NeWord.append_prod** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.Ne
Word`。
形式化陈述：append_prod {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k 
l} : (append w₁ hne w₂).prod = w₁.prod * w₂.prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem append_prod {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).prod = w₁.prod * w₂.prod := by simp [toWord, prod, Word.prod]

/-- One can replace the first letter in a non-empty reduced word by an element of the same
group -/
/-
**Monoid.CoprodI.NeWord.replaceHead** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.Ne
Word`。
形式化陈述：{ι : Type u_1} →   {M : ι → Type u_2} →     [inst : (i : ι) → Monoid (M i)
] →       {i j : ι} → (x : M i) → x ≠ 1 → Monoid.CoprodI.NeWord M i j → Monoid.C
oprodI.NeWord M i j
参数：i : ι；M i；x : M i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One can replace the first letter in a non-empty reduced word by an element of th
e same
group
-/
def replaceHead : ∀ {i j : ι} (x : M i) (_hnotone : x ≠ 1) (_w : NeWord M i j), NeWord M i j
  | _, _, x, h, singleton _ _ => singleton x h
  | _, _, x, h, append w₁ hne w₂ => append (replaceHead x h w₁) hne w₂

@[simp]
/-
**Monoid.CoprodI.NeWord.replaceHead_head** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Copro
dI.NeWord`。
形式化陈述：replaceHead_head {i j : ι} (x : M i) (hnotone : x != 1) (w : NeWord M i j)
 : (replaceHead x hnotone w).head = x
参数：x : M i；hnotone : x != 1；w : NeWord M i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.NeWord.head.eq_2`：∀ {ι : Type u_1} {M : ι → Type u_2} [in
st : (i : ι) → Monoid (M i)] (x x_1 j k : ι) (_hne : j ≠ k)   (w₁ : Monoid.Copro
dI.NeWord M x j) (w₂ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem replaceHead_head {i j : ι} (x : M i) (hnotone : x ≠ 1) (w : NeWord M i j) :
    (replaceHead x hnotone w).head = x := by
  induction w
  · rfl
  · simp [*, replaceHead]

/-- One can multiply an element from the left to a non-empty reduced word if it does not cancel
with the first element in the word. -/
/-
**Monoid.CoprodI.NeWord.mulHead** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.NeWord
`。
形式化陈述：mulHead {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1)
 : NeWord M i j
参数：w : NeWord M i j；x : M i；hnotone : x * w.head != 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One can multiply an element from the left to a non-empty reduced word if it does
 not cancel
with the first element in the word.
-/
def mulHead {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) : NeWord M i j :=
  replaceHead (x * w.head) hnotone w

@[simp]
/-
**Monoid.CoprodI.NeWord.mulHead_head** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.N
eWord`。
形式化陈述：mulHead_head {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head 
!= 1) : (mulHead w x hnotone).head = x * w.head
参数：w : NeWord M i j；x : M i；hnotone : x * w.head != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.NeWord.replaceHead_head`：replaceHead_head {i j : ι} (x : 
M i) (hnotone : x != 1) (w : NeWord M i j) : (replaceHead x hnotone w).head = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulHead_head {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
    (mulHead w x hnotone).head = x * w.head := by
  induction w
  · rfl
  · simp [*, mulHead]

@[simp]
/-
**Monoid.CoprodI.NeWord.mulHead_prod** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.N
eWord`。
形式化陈述：mulHead_prod {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head 
!= 1) : (mulHead w x hnotone).prod = of x * w.prod
参数：w : NeWord M i j；x : M i；hnotone : x * w.head != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.NeWord.prod_singleton`：prod_singleton {i} (x : M i) (hne_
one : x != 1) : (singleton x hne_one).prod = of x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Monoid.CoprodI.NeWord.append_prod`：append_prod {i j k l} {w₁ : NeWord M 
i j} {hne : j != k} {w₂ : NeWord M k l} : (append w₁ hne w₂).prod = w₁.prod * w₂
.prod
-/
theorem mulHead_prod {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
    (mulHead w x hnotone).prod = of x * w.prod := by
  unfold mulHead
  induction w with
  | singleton => simp [replaceHead]
  | append _ _ _ w_ih_w₁ w_ih_w₂ =>
    specialize w_ih_w₁ _ hnotone
    simp only [replaceHead, append_prod, ← mul_assoc]
    congr 1

section Group

variable {G : ι → Type*} [∀ i, Group (G i)]

/-- The inverse of a non-empty reduced word -/
/-
**Monoid.CoprodI.NeWord.inv** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.CoprodI.NeWord`。
形式化陈述：{ι : Type u_1} →   {G : ι → Type u_4} →     [inst : (i : ι) → Group (G i)]
 → {i j : ι} → Monoid.CoprodI.NeWord G i j → Monoid.CoprodI.NeWord G j i
参数：i : ι；G i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a non-empty reduced word
-/
def inv : ∀ {i j} (_w : NeWord G i j), NeWord G j i
  | _, _, singleton x h => singleton x⁻¹ (mt inv_eq_one.mp h)
  | _, _, append w₁ h w₂ => append w₂.inv h.symm w₁.inv

@[simp]
/-
**Monoid.CoprodI.NeWord.inv_prod** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.NeWor
d`。
形式化陈述：inv_prod {i j} (w : NeWord G i j) : w.inv.prod = w.prod⁻¹
参数：w : NeWord G i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.NeWord.prod_singleton`：prod_singleton {i} (x : M i) (hne_
one : x != 1) : (singleton x hne_one).prod = of x
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Monoid.CoprodI.NeWord.append_prod`：append_prod {i j k l} {w₁ : NeWord M 
i j} {hne : j != k} {w₂ : NeWord M k l} : (append w₁ hne w₂).prod = w₁.prod * w₂
.prod
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
theorem inv_prod {i j} (w : NeWord G i j) : w.inv.prod = w.prod⁻¹ := by
  induction w <;> simp [inv, *]

@[simp]
/-
**Monoid.CoprodI.NeWord.inv_head** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.NeWor
d`。
形式化陈述：inv_head {i j} (w : NeWord G i j) : w.inv.head = w.last⁻¹
参数：w : NeWord G i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.NeWord.head.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_2} [in
st : (i : ι) → Monoid (M i)] (x : ι) (x_3 : M x) (a : x_3 ≠ 1),   (Monoid.Coprod
I.NeWord.singleton x_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Monoid.CoprodI.NeWord.head.eq_2`：∀ {ι : Type u_1} {M : ι → Type u_2} [in
st : (i : ι) → Monoid (M i)] (x x_1 j k : ι) (_hne : j ≠ k)   (w₁ : Monoid.Copro
dI.NeWord M x j) (w₂ …
-/
theorem inv_head {i j} (w : NeWord G i j) : w.inv.head = w.last⁻¹ := by
  induction w <;> simp [inv, *]

@[simp]
/-
**Monoid.CoprodI.NeWord.inv_last** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI.NeWor
d`。
形式化陈述：inv_last {i j} (w : NeWord G i j) : w.inv.last = w.head⁻¹
参数：w : NeWord G i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.NeWord.last.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_2} [in
st : (i : ι) → Monoid (M i)] (x : ι) (x_3 : M x) (a : x_3 ≠ 1),   (Monoid.Coprod
I.NeWord.singleton x_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Monoid.CoprodI.NeWord.last.eq_2`：∀ {ι : Type u_1} {M : ι → Type u_2} [in
st : (i : ι) → Monoid (M i)] (x x_1 j k : ι) (_hne : j ≠ k)   (w₁ : Monoid.Copro
dI.NeWord M x j) (w₂ …
-/
theorem inv_last {i j} (w : NeWord G i j) : w.inv.last = w.head⁻¹ := by
  induction w <;> simp [inv, *]

end Group

end NeWord

section PingPongLemma

open Cardinal
open scoped Function -- required for scoped `on` notation
open scoped Pointwise

variable {G : Type*} [Group G]
variable {H : ι → Type*} [∀ i, Group (H i)]
variable (f : ∀ i, H i →* G)

-- We need many groups or one group with many elements
variable (hcard : 3 ≤ #ι ∨ ∃ i, 3 ≤ #(H i))

-- A group action on α, and the ping-pong sets
variable {α : Type*} [MulAction G α]
variable (X : ι → Set α)
variable (hXnonempty : ∀ i, (X i).Nonempty)
variable (hXdisj : Pairwise (Disjoint on X))
variable (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i)
include hpp

/-
**Monoid.CoprodI.lift_word_ping_pong** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.CoprodI`。
形式化陈述：lift_word_ping_pong {i j k} (w : NeWord H i j) (hk : j != k) : lift f w.pr
od • X k subseteq X i
参数：w : NeWord H i j；hk : j != k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Monoid.CoprodI.NeWord.prod_singleton`：prod_singleton {i} (x : M i) (hne_
one : x != 1) : (singleton x hne_one).prod = of x
· 使用定理 `Monoid.CoprodI.lift_of`：lift_of {N} [Monoid N] (fi : forall i, M i ->* N
) {i} (m : M i) : lift fi (of m) = fi i m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Monoid.CoprodI.NeWord.append_prod`：append_prod {i j k l} {w₁ : NeWord M 
i j} {hne : j != k} {w₂ : NeWord M k l} : (append w₁ hne w₂).prod = w₁.prod * w₂
.prod
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
theorem lift_word_ping_pong {i j k} (w : NeWord H i j) (hk : j ≠ k) :
    lift f w.prod • X k ⊆ X i := by
  induction w generalizing k with
  | singleton x hne_one => simpa using hpp hk _ hne_one
  | @append i j k l w₁ hne w₂ hIw₁ hIw₂ =>
    calc
      lift f (NeWord.append w₁ hne w₂).prod • X k = lift f w₁.prod • lift f w₂.prod • X k := by
        simp [mul_smul]
      _ ⊆ lift f w₁.prod • X _ := smul_set_subset_smul_set_iff.mpr (hIw₂ hk)
      _ ⊆ X i := hIw₁ hne

include hXnonempty hXdisj
/-
**Monoid.CoprodI.lift_word_prod_nontrivial_of_other_i** 是 Mathlib 中的一个定理，位于命名空间 
`Monoid.CoprodI`。
形式化陈述：lift_word_prod_nontrivial_of_other_i {i j k} (w : NeWord H i j) (hhead : k
 != i) (hlast : k != j) : lift f w.prod != 1
参数：w : NeWord H i j；hhead : k != i；hlast : k != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Monoid.CoprodI.lift_word_ping_pong`：lift_word_ping_pong {i j k} (w : NeW
ord H i j) (hk : j != k) : lift f w.prod • X k subseteq X i
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
-/
theorem lift_word_prod_nontrivial_of_other_i {i j k} (w : NeWord H i j) (hhead : k ≠ i)
    (hlast : k ≠ j) : lift f w.prod ≠ 1 := by
  intro heq1
  have : X k ⊆ X i := by simpa [heq1] using lift_word_ping_pong f X hpp w hlast.symm
  obtain ⟨x, hx⟩ := hXnonempty k
  exact (hXdisj hhead).le_bot ⟨hx, this hx⟩

variable [Nontrivial ι]
/-
**Monoid.CoprodI.lift_word_prod_nontrivial_of_head_eq_last** 是 Mathlib 中的一个定理，位于
命名空间 `Monoid.CoprodI`。
形式化陈述：lift_word_prod_nontrivial_of_head_eq_last {i} (w : NeWord H i i) : lift f 
w.prod != 1
参数：w : NeWord H i i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Monoid.CoprodI.lift_word_prod_nontrivial_of_other_i`：lift_word_prod_nont
rivial_of_other_i {i j k} (w : NeWord H i j) (hhead : k != i) (hlast : k != j) :
 lift f w.prod != 1
-/
theorem lift_word_prod_nontrivial_of_head_eq_last {i} (w : NeWord H i i) :
    lift f w.prod ≠ 1 := by
  obtain ⟨k, hk⟩ := exists_ne i
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hk hk
/-
**Monoid.CoprodI.lift_word_prod_nontrivial_of_head_card** 是 Mathlib 中的一个定理，位于命名空
间 `Monoid.CoprodI`。
形式化陈述：lift_word_prod_nontrivial_of_head_card {i j} (w : NeWord H i j) (hcard : 3
 <= #(H i)) (hheadtail : i != j) : lift f w.prod != 1
参数：w : NeWord H i j；hcard : 3 <= #(H i)；hheadtail : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.exists_ne_ne_of_three_le`：exists_ne_ne_of_three_le {α : Type*} 
(h : 3 <= #α) (x y : α) : exists z : α, z != x ∧ z != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `div_ne_one_of_ne`：div_ne_one_of_ne : a != b -> a / b != 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_ne_one`：inv_ne_one : a⁻¹ != 1 ↔ a != 1
· 使用定理 `Monoid.CoprodI.lift_word_prod_nontrivial_of_head_eq_last`：lift_word_prod
_nontrivial_of_head_eq_last {i} (w : NeWord H i i) : lift f w.prod != 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Monoid.CoprodI.NeWord.append_prod`：append_prod {i j k l} {w₁ : NeWord M 
i j} {hne : j != k} {w₂ : NeWord M k l} : (append w₁ hne w₂).prod = w₁.prod * w₂
.prod
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Monoid.CoprodI.NeWord.mulHead_prod`：mulHead_prod {i j : ι} (w : NeWord M
 i j) (x : M i) (hnotone : x * w.head != 1) : (mulHead w x hnotone).prod = of x 
* w.prod
· 使用定理 `Monoid.CoprodI.NeWord.prod_singleton`：prod_singleton {i} (x : M i) (hne_
one : x != 1) : (singleton x hne_one).prod = of x
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Monoid.CoprodI.lift_of`：lift_of {N} [Monoid N] (fi : forall i, M i ->* N
) {i} (m : M i) : lift fi (of m) = fi i m
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_word_prod_nontrivial_of_head_card {i j} (w : NeWord H i j)
    (hcard : 3 ≤ #(H i)) (hheadtail : i ≠ j) : lift f w.prod ≠ 1 := by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.exists_ne_ne_of_three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head ≠ 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : NeWord H i i :=
    NeWord.append (NeWord.mulHead w h hnot1) hheadtail.symm
      (NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
  have hw' : lift f w'.prod ≠ 1 :=
    lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w'
  intro heq1
  apply hw'
  simp [w', heq1]

include hcard in
/-
**Monoid.CoprodI.lift_word_prod_nontrivial_of_not_empty** 是 Mathlib 中的一个定理，位于命名空
间 `Monoid.CoprodI`。
形式化陈述：lift_word_prod_nontrivial_of_not_empty {i j} (w : NeWord H i j) : lift f w
.prod != 1
参数：w : NeWord H i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.exists_ne_ne_of_three_le`：exists_ne_ne_of_three_le {α : Type*} 
(h : 3 <= #α) (x y : α) : exists z : α, z != x ∧ z != y
· 使用定理 `Monoid.CoprodI.lift_word_prod_nontrivial_of_other_i`：lift_word_prod_nont
rivial_of_other_i {i j k} (w : NeWord H i j) (hhead : k != i) (hlast : k != j) :
 lift f w.prod != 1
· 使用定理 `Monoid.CoprodI.lift_word_prod_nontrivial_of_head_eq_last`：lift_word_prod
_nontrivial_of_head_eq_last {i} (w : NeWord H i i) : lift f w.prod != 1
· 使用定理 `Monoid.CoprodI.lift_word_prod_nontrivial_of_head_card`：lift_word_prod_no
ntrivial_of_head_card {i j} (w : NeWord H i j) (hcard : 3 <= #(H i)) (hheadtail 
: i != j) : lift f w.prod != 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.NeWord.inv_prod`：inv_prod {i j} (w : NeWord G i j) : w.in
v.prod = w.prod⁻¹
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
theorem lift_word_prod_nontrivial_of_not_empty {i j} (w : NeWord H i j) :
    lift f w.prod ≠ 1 := by
  rcases hcard with hcard | hcard
  · obtain ⟨i, h1, h2⟩ := Cardinal.exists_ne_ne_of_three_le hcard i j
    exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w h1 h2
  · obtain ⟨k, hcard⟩ := hcard
    by_cases hh : i = k <;> by_cases hl : j = k
    · subst hh
      subst hl
      exact lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w
    · subst hh
      change j ≠ i at hl
      exact lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w hcard hl.symm
    · subst hl
      change i ≠ j at hh
      have : lift f w.inv.prod ≠ 1 :=
        lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w.inv hcard hh.symm
      intro heq
      apply this
      simpa using heq
    · change i ≠ k at hh
      change j ≠ k at hl
      exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hh.symm hl.symm

include hcard in
/-
**Monoid.CoprodI.empty_of_word_prod_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Cop
rodI`。
形式化陈述：empty_of_word_prod_eq_one {w : Word H} (h : lift f w.prod = 1) : w = Word.
empty
参数：h : lift f w.prod = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Monoid.CoprodI.NeWord.of_word`：of_word (w : Word M) (h : w != empty) : e
xists (i j : _) (w' : NeWord M i j), w'.toWord = w
· 使用定理 `Monoid.CoprodI.lift_word_prod_nontrivial_of_not_empty`：lift_word_prod_no
ntrivial_of_not_empty {i j} (w : NeWord H i j) : lift f w.prod != 1
-/
theorem empty_of_word_prod_eq_one {w : Word H} (h : lift f w.prod = 1) :
    w = Word.empty := by
  by_contra hnotempty
  obtain ⟨i, j, w, rfl⟩ := NeWord.of_word w hnotempty
  exact lift_word_prod_nontrivial_of_not_empty f hcard X hXnonempty hXdisj hpp w h

set_option backward.isDefEq.respectTransparency false in
include hcard in
/-- The **Ping-Pong-Lemma**.

Given a group action of `G` on `X` so that the `H i` acts in a specific way on disjoint subsets
`X i` we can prove that `lift f` is injective, and thus the image of `lift f` is isomorphic to the
free product of the `H i`.

Often the Ping-Pong-Lemma is stated with regard to subgroups `H i` that generate the whole group;
we generalize to arbitrary group homomorphisms `f i : H i →* G` and do not require the group to be
generated by the images.

Usually the Ping-Pong-Lemma requires that one group `H i` has at least three elements. This
condition is only needed if `# ι = 2`, and we accept `3 ≤ # ι` as an alternative.
-/
/-
**Monoid.CoprodI.lift_injective_of_ping_pong** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.C
oprodI`。
形式化陈述：lift_injective_of_ping_pong : Function.Injective (lift f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_one`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9}
 [inst : Group G] [inst_1 : MulOneClass H] [inst_2 : FunLike F G H]   [MonoidHom
Class F G H] (…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `Monoid.CoprodI.empty_of_word_prod_eq_one`：empty_of_word_prod_eq_one {w :
 Word H} (h : lift f w.prod = 1) : w = Word.empty
· 使用定理 `Monoid.CoprodI.Word.prod_empty`：prod_empty : prod (empty : Word M) = 1

--- 原说明 ---
The **Ping-Pong-Lemma**.

Given a group action of `G` on `X` so that the `H i` acts in a specific way on d
isjoint subsets
`X i` we can prove that `lift f` is injective, and thus the image of `lift f` is
 isomorphic to the
free product of the `H i`.

Often the Ping-Pong-Lemma is stated with regard to subgroups `H i` that generate
 the whole group;
we generalize to arbitrary group homomorphisms `f i : H i →* G` and do not requi
re the group to be
generated by the images.

Usually the Ping-Pong-Lemma requires that one group `H i` has at least three ele
ments. This
condition is only needed if `# ι = 2`, and we accept `3 ≤ # ι` as an alternative
.
-/
theorem lift_injective_of_ping_pong : Function.Injective (lift f) := by
  classical
    apply (injective_iff_map_eq_one (lift f)).mpr
    rw [(CoprodI.Word.equiv).forall_congr_left]
    intro w Heq
    dsimp [Word.equiv] at *
    rw [empty_of_word_prod_eq_one f hcard X hXnonempty hXdisj hpp Heq, Word.prod_empty]

end PingPongLemma

/-- Given a family of free groups with distinguished bases, then their free product is free, with
a basis given by the union of the bases of the components. -/
/-
**Monoid.CoprodI.FreeGroupBasis.coprodI** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod
I.FreeGroupBasis`。
形式化陈述：{ι : Type u_4} →   {X : ι → Type u_5} →     {G : ι → Type u_6} →       [in
st : (i : ι) → Group (G i)] →         ((i : ι) → FreeGroupBasis (X i) (G i)) → F
reeGroupBasis ((i : ι) × X i) (Monoid.CoprodI G)
参数：i : ι；G i；(i : ι) → FreeGroupBasis (X i) (G i)；(i : ι) × X i；Monoid.CoprodI G
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of free groups with distinguished bases, then their free product 
is free, with
a basis given by the union of the bases of the components.
-/
def FreeGroupBasis.coprodI {ι : Type*} {X : ι → Type*} {G : ι → Type*} [∀ i, Group (G i)]
    (B : ∀ i, FreeGroupBasis (X i) (G i)) :
    FreeGroupBasis (Σ i, X i) (CoprodI G) :=
  ⟨MulEquiv.symm <| MonoidHom.toMulEquiv
    (FreeGroup.lift fun x : Σ i, X i => CoprodI.of (B x.1 x.2))
    (CoprodI.lift fun i : ι => (B i).lift fun x : X i =>
              FreeGroup.of (⟨i, x⟩ : Σ i, X i))
    (by ext; simp)
    (by ext1 i; apply (B i).ext_hom; simp)⟩

/-- The free product of free groups is itself a free group. -/
/-
**Monoid.CoprodI.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.CoprodI`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free product of free groups is itself a free group.
-/
instance {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)] [∀ i, IsFreeGroup (G i)] :
    IsFreeGroup (CoprodI G) :=
  (FreeGroupBasis.coprodI (fun i ↦ IsFreeGroup.basis (G i))).isFreeGroup

-- NB: One might expect this theorem to be phrased with ℤ, but ℤ is an additive group,
-- and using `Multiplicative ℤ` runs into diamond issues.
/-- A free group is a free product of copies of the `FreeGroup` over one generator. -/
@[simps!]
/-
**Monoid.CoprodI._root_.freeGroupEquivCoprodI** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.
CoprodI`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A free group is a free product of copies of the `FreeGroup` over one generator.
-/
def _root_.freeGroupEquivCoprodI {ι : Type u_1} :
    FreeGroup ι ≃* CoprodI fun _ : ι => FreeGroup Unit := by
  refine MonoidHom.toMulEquiv ?_ ?_ ?_ ?_
  · exact FreeGroup.lift fun i => @CoprodI.of ι _ _ i (FreeGroup.of Unit.unit)
  · exact CoprodI.lift fun i => FreeGroup.lift fun _ => FreeGroup.of i
  · ext; simp
  · ext i a; cases a; simp

section PingPongLemma

open Cardinal
open scoped Function -- required for scoped `on` notation
open scoped Pointwise

variable [Nontrivial ι]
variable {G : Type u_1} [Group G] (a : ι → G)

-- A group action on α, and the ping-pong sets
variable {α : Type*} [MulAction G α]
variable (X Y : ι → Set α)
variable (hXnonempty : ∀ i, (X i).Nonempty)
variable (hXdisj : Pairwise (Disjoint on X))
variable (hYdisj : Pairwise (Disjoint on Y))
variable (hXYdisj : ∀ i j, Disjoint (X i) (Y j))
variable (hX : ∀ i, a i • (Y i)ᶜ ⊆ X i)
variable (hY : ∀ i, a⁻¹ i • (X i)ᶜ ⊆ Y i)

set_option backward.isDefEq.respectTransparency false in
include hXnonempty hXdisj hYdisj hXYdisj hX hY in
/-- The Ping-Pong-Lemma.

Given a group action of `G` on `X` so that the generators of the free groups act in specific
ways on disjoint subsets `X i` and `Y i` we can prove that `lift f` is injective, and thus the image
of `lift f` is isomorphic to the free group.

Often the Ping-Pong-Lemma is stated with regard to group elements that generate the whole group;
we generalize to arbitrary group homomorphisms from the free group to `G` and do not require the
group to be generated by the elements.
-/
/-
**Monoid.CoprodI._root_.FreeGroup.injective_lift_of_ping_pong** 是 Mathlib 中的一个定理
，位于命名空间 `Monoid.CoprodI`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Ping-Pong-Lemma.

Given a group action of `G` on `X` so that the generators of the free groups act
 in specific
ways on disjoint subsets `X i` and `Y i` we can prove that `lift f` is injective
, and thus the image
of `lift f` is isomorphic to the free group.

Often the Ping-Pong-Lemma is stated with regard to group elements that generate 
the whole group;
we generalize to arbitrary group homomorphisms from the free group to `G` and do
 not require the
group to be generated by the elements.
-/
theorem _root_.FreeGroup.injective_lift_of_ping_pong : Function.Injective (FreeGroup.lift a) := by
  -- Step one: express the free group lift via the free product lift
  have : FreeGroup.lift a =
      (CoprodI.lift fun i => FreeGroup.lift fun _ => a i).comp
        (@freeGroupEquivCoprodI ι).toMonoidHom := by
    ext i
    simp
  rw [this, MonoidHom.coe_comp]
  clear this
  refine Function.Injective.comp ?_ (MulEquiv.injective freeGroupEquivCoprodI)
  -- Step two: Invoke the ping-pong lemma for free products
  change Function.Injective (lift fun i : ι => FreeGroup.lift fun _ => a i)
  -- Prepare to instantiate lift_injective_of_ping_pong
  let H : ι → Type _ := fun _i => FreeGroup Unit
  let f : ∀ i, H i →* G := fun i => FreeGroup.lift fun _ => a i
  let X' : ι → Set α := fun i => X i ∪ Y i
  apply lift_injective_of_ping_pong f _ X'
  · show ∀ i, (X' i).Nonempty
    exact fun i => Set.Nonempty.inl (hXnonempty i)
  · show Pairwise (Disjoint on X')
    intro i j hij
    simp only [X']
    apply Disjoint.union_left <;> apply Disjoint.union_right
    · exact hXdisj hij
    · exact hXYdisj i j
    · exact (hXYdisj j i).symm
    · exact hYdisj hij
  · change Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X' j ⊆ X' i
    rintro i j hij
    -- use free_group unit ≃ ℤ
    refine FreeGroup.freeGroupUnitEquivInt.forall_congr_left.mpr ?_
    intro n hne1
    change FreeGroup.lift (fun _ => a i) (FreeGroup.of () ^ n) • X' j ⊆ X' i
    simp only [map_zpow, FreeGroup.lift_apply_of]
    change a i ^ n • X' j ⊆ X' i
    have hnne0 : n ≠ 0 := by
      rintro rfl
      apply hne1
      simp [H, FreeGroup.freeGroupUnitEquivInt]
    clear hne1
    simp only [X']
    -- Positive and negative powers separately
    rcases (lt_or_gt_of_ne hnne0).symm with hlt | hgt
    · have h1n : 1 ≤ n := hlt
      calc
        a i ^ n • X' j ⊆ a i ^ n • (Y i)ᶜ :=
          smul_set_mono ((hXYdisj j i).union_left <| hYdisj hij.symm).subset_compl_right
        _ ⊆ X i := by
          clear hnne0 hlt
          induction n, h1n using Int.leInduction with
          | base => rw [zpow_one]; exact hX i
          | succ n _hle hi =>
            calc
              a i ^ (n + 1) • (Y i)ᶜ = (a i ^ n * a i) • (Y i)ᶜ := by rw [zpow_add, zpow_one]
              _ = a i ^ n • a i • (Y i)ᶜ := mul_smul _ _ _
              _ ⊆ a i ^ n • X i := smul_set_mono <| hX i
              _ ⊆ a i ^ n • (Y i)ᶜ := smul_set_mono (hXYdisj i i).subset_compl_right
              _ ⊆ X i := hi
        _ ⊆ X' i := Set.subset_union_left
    · have h1n : n ≤ -1 := by
        apply Int.le_of_lt_add_one
        simpa using hgt
      calc
        a i ^ n • X' j ⊆ a i ^ n • (X i)ᶜ :=
          smul_set_mono ((hXdisj hij.symm).union_left (hXYdisj i j).symm).subset_compl_right
        _ ⊆ Y i := by
          clear hnne0 hgt
          induction n, h1n using Int.leInductionDown with
          | base => rw [zpow_neg, zpow_one]; exact hY i
          | pred n hle hi =>
            calc
              a i ^ (n - 1) • (X i)ᶜ = (a i ^ n * (a i)⁻¹) • (X i)ᶜ := by rw [zpow_sub, zpow_one]
              _ = a i ^ n • (a i)⁻¹ • (X i)ᶜ := mul_smul _ _ _
              _ ⊆ a i ^ n • Y i := smul_set_mono <| hY i
              _ ⊆ a i ^ n • (X i)ᶜ := smul_set_mono (hXYdisj i i).symm.subset_compl_right
              _ ⊆ Y i := hi
        _ ⊆ X' i := Set.subset_union_right
  show _ ∨ ∃ i, 3 ≤ #(H i)
  inhabit ι
  right
  use Inhabited.default
  simp only [H]
  rw [FreeGroup.freeGroupUnitEquivInt.cardinal_eq, Cardinal.mk_denumerable]
  exact natCast_le_aleph0

end PingPongLemma

end Monoid.CoprodI

