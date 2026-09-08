/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Topology.Category.Profinite.Nobeling.Basic

/-!
# The zero and limit cases in the induction for Nöbeling's theorem

This file proves the zero and limit cases of the ordinal induction used in the proof of
Nöbeling's theorem. See the section docstrings for more information.

For the overall proof outline see `Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool)) [LinearOrder I]

section Zero
/-!
## The zero case of the induction

In this case, we have `contained C 0` which means that `C` is either empty or a singleton.
-/

/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## The zero case of the induction

In this case, we have `contained C 0` which means that `C` is either empty or a 
singleton.
-/
instance : Subsingleton (LocallyConstant (∅ : Set (I → Bool)) ℤ) :=
  subsingleton_iff.mpr (fun _ _ ↦ LocallyConstant.ext isEmptyElim)
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEmpty { l // Products.isGood (∅ : Set (I → Bool)) l } :=
  isEmpty_iff.mpr fun ⟨l, hl⟩ ↦ hl <| by
    rw [subsingleton_iff.mp inferInstance (Products.eval ∅ l) 0]
    exact Submodule.zero_mem _
/-
**Profinite.NobelingProof.GoodProducts.linearIndependentEmpty** 是 Mathlib 中的一个定理
，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u_1} [inst : LinearOrder I], LinearIndependent ℤ (Profinite.No
belingProof.GoodProducts.eval ∅)
参数：Profinite.NobelingProof.GoodProducts.eval ∅。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_empty_type`：linearIndependent_empty_type [IsEmpty ι] :
 LinearIndependent R v
· 使用定理 `Profinite.NobelingProof.instIsEmptySubtypeProductsIsGoodEmptyCollectionS
etForallBool`：∀ {I : Type u} [inst : LinearOrder I], IsEmpty { l // Profinite.No
belingProof.Products.isGood ∅ l }
-/
theorem GoodProducts.linearIndependentEmpty {I} [LinearOrder I] :
    LinearIndependent ℤ (eval (∅ : Set (I → Bool))) := linearIndependent_empty_type

/-- The empty list as a `Products` -/
/-
**Profinite.NobelingProof.Products.nil** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobe
lingProof.Products`。
形式化陈述：{I : Type u} → [inst : LinearOrder I] → Profinite.NobelingProof.Products I
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty list as a `Products`
-/
def Products.nil : Products I := ⟨[], by simp only [List.isChain_nil]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.Products.lt_nil_empty** 是 Mathlib 中的一个定理，位于命名空间 `Profi
nite.NobelingProof.Products`。
形式化陈述：∀ {I : Type u_1} [inst : LinearOrder I], {m | m < Profinite.NobelingProof.
Products.nil} = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Products.lt_nil_empty {I} [LinearOrder I] : { m : Products I | m < Products.nil } = ∅ := by
  ext ⟨m, hm⟩
  refine ⟨fun h ↦ ?_, by tauto⟩
  simp only [Set.mem_ofPred_eq, lt_iff_lex_lt, nil, List.not_lex_nil] at h
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [TopologicalSpace α] [Nonempty α] : Nontrivial (LocallyConstant α ℤ) :=
  ⟨0, 1, ne_of_apply_ne DFunLike.coe <| (Function.const_injective (β := ℤ)).ne zero_ne_one⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.Products.isGood_nil** 是 Mathlib 中的一个定理，位于命名空间 `Profini
te.NobelingProof.Products`。
形式化陈述：∀ {I : Type u_1} [inst : LinearOrder I],   Profinite.NobelingProof.Product
s.isGood {fun x => false} Profinite.NobelingProof.Products.nil
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Profinite.NobelingProof.instNontrivialLocallyConstantIntOfNonempty`：∀ {α
 : Type u_1} [inst : TopologicalSpace α] [Nonempty α], Nontrivial (LocallyConsta
nt α ℤ)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem Products.isGood_nil {I} [LinearOrder I] :
    Products.isGood ({fun _ ↦ false} : Set (I → Bool)) Products.nil := by
  intro h
  simp [Products.eval, Products.nil] at h
/-
**Profinite.NobelingProof.Products.span_nil_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Pr
ofinite.NobelingProof.Products`。
形式化陈述：∀ {I : Type u_1} [inst : LinearOrder I],   Submodule.span ℤ (Profinite.Nob
elingProof.Products.eval {fun x => false} '' {Profinite.NobelingProof.Products.n
il}) =     ⊤
参数：Profinite.NobelingProof.Products.eval {fun x => false} '' {Profinite.Nobeling
Proof.Products.nil}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem Products.span_nil_eq_top {I} [LinearOrder I] :
    Submodule.span ℤ (eval ({fun _ ↦ false} : Set (I → Bool)) '' {nil}) = ⊤ := by
  rw [Set.image_singleton, eq_top_iff]
  intro f _
  rw [Submodule.mem_span_singleton]
  refine ⟨f default, ?_⟩
  simp only [eval, List.map, List.prod_nil, zsmul_eq_mul, mul_one, Products.nil]
  ext x
  obtain rfl : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- There is a unique `GoodProducts` for the singleton `{fun _ ↦ false}`. -/
noncomputable
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique { l // Products.isGood ({fun _ ↦ false} : Set (I → Bool)) l } where
  default := ⟨Products.nil, Products.isGood_nil⟩
  uniq := by
    intro ⟨⟨l, hl⟩, hll⟩
    ext
    apply Subtype.ext
    apply (List.lex_nil_or_eq_nil l (r := (· < ·))).resolve_left
    intro _
    apply hll
    have he : {Products.nil} ⊆ {m | m < ⟨l,hl⟩} := by
      simpa only [Products.nil, Products.lt_iff_lex_lt, Set.singleton_subset_iff, Set.mem_ofPred_eq]
    grw [← he]
    rw [Products.span_nil_eq_top]
    exact Submodule.mem_top
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [TopologicalSpace α] : IsAddTorsionFree (LocallyConstant α ℤ) :=
  LocallyConstant.coe_injective.isAddTorsionFree LocallyConstant.coeFnAddMonoidHom
/-
**Profinite.NobelingProof.GoodProducts.linearIndependentSingleton** 是 Mathlib 中的
一个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u_1} [inst : LinearOrder I],   LinearIndependent ℤ (Profinite.
NobelingProof.GoodProducts.eval {fun x => false})
参数：Profinite.NobelingProof.GoodProducts.eval {fun x => false}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndependent.of_subsingleton`：LinearIndependent.of_subsingleton [Su
bsingleton ι] (i : ι) (hi : v i != 0) : LinearIndependent R v
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `Profinite.NobelingProof.instIsAddTorsionFreeLocallyConstantInt`：∀ (α : T
ype u_1) [inst : TopologicalSpace α], IsAddTorsionFree (LocallyConstant α ℤ)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Profinite.NobelingProof.instNontrivialLocallyConstantIntOfNonempty`：∀ {α
 : Type u_1} [inst : TopologicalSpace α] [Nonempty α], Nontrivial (LocallyConsta
nt α ℤ)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem GoodProducts.linearIndependentSingleton {I} [LinearOrder I] :
    LinearIndependent ℤ (eval ({fun _ ↦ false} : Set (I → Bool))) :=
  .of_subsingleton default <| by simp [eval, Products.eval, Products.nil, default]

end Zero

variable [WellFoundedLT I]

section Limit
/-!
## The limit case of the induction

We relate linear independence in `LocallyConstant (π C (ord I · < o')) ℤ` with linear independence
in `LocallyConstant C ℤ`, where `contained C o` and `o' < o`.

When `o` is a limit ordinal, we prove that the good products in `LocallyConstant C ℤ` are linearly
independent if and only if a certain directed union is linearly independent. Each term in this
directed union is in bijection with the good products w.r.t. `π C (ord I · < o')` for an ordinal
`o' < o`, and these are linearly independent by the inductive hypothesis.

### Main definitions

* `GoodProducts.smaller` is the image of good products coming from a smaller ordinal.

* `GoodProducts.range_equiv`: The image of the `GoodProducts` in `C` is equivalent to the union of
  `smaller C o'` over all ordinals `o' < o`.

### Main results

* `Products.limitOrdinal`: for `o` a limit ordinal such that `contained C o`, a product `l` is good
  w.r.t. `C` iff it there exists an ordinal `o' < o` such that `l` is good w.r.t.
  `π C (ord I · < o')`.

* `GoodProducts.linearIndependent_iff_union_smaller` is the result mentioned above, that the good
  products are linearly independent iff a directed union is.
-/

namespace GoodProducts

/--
The image of the `GoodProducts` for `π C (ord I · < o)` in `LocallyConstant C ℤ`. The name `smaller`
refers to the setting in which we will use this, when we are mapping in `GoodProducts` from a
smaller set, i.e. when `o` is a smaller ordinal than the one `C` is "contained" in.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Profinite.NobelingProof.GoodProducts.smaller** 是 Mathlib 中的一个定义，位于命名空间 `Profin
ite.NobelingProof.GoodProducts`。
形式化陈述：smaller (o : Ordinal) : Set (LocallyConstant C Int)
参数：o : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def smaller (o : Ordinal) : Set (LocallyConstant C ℤ) :=
  (πs C o) '' (range (π C (ord I · < o)))

/--
The map from the image of the `GoodProducts` in `LocallyConstant (π C (ord I · < o)) ℤ` to
`smaller C o`
-/
noncomputable
/-
**Profinite.NobelingProof.GoodProducts.range_equiv_smaller_toFun** 是 Mathlib 中的一
个定义，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：range_equiv_smaller_toFun (o : Ordinal) (x : range (π C (ord I · < o))) : 
smaller C o
参数：o : Ordinal；x : range (π C (ord I · < o))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def range_equiv_smaller_toFun (o : Ordinal) (x : range (π C (ord I · < o))) : smaller C o :=
  ⟨πs C o ↑x, x.val, x.property, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.GoodProducts.range_equiv_smaller_toFun_bijective** 是 M
athlib 中的一个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：range_equiv_smaller_toFun_bijective (o : Ordinal) : Function.Bijective (ra
nge_equiv_smaller_toFun C o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Profinite.NobelingProof.injective_πs`：injective_πs (o : Ordinal) : Funct
ion.Injective (πs C o)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem range_equiv_smaller_toFun_bijective (o : Ordinal) :
    Function.Bijective (range_equiv_smaller_toFun C o) := by
  dsimp +unfoldPartialApp [range_equiv_smaller_toFun]
  refine ⟨fun a b hab ↦ ?_, fun ⟨a, b, hb⟩ ↦ ?_⟩
  · ext1
    simp only [Subtype.mk.injEq] at hab
    exact injective_πs C o hab
  · use ⟨b, hb.1⟩
    simpa only [Subtype.mk.injEq] using hb.2

/--
The equivalence from the image of the `GoodProducts` in `LocallyConstant (π C (ord I · < o)) ℤ` to
`smaller C o`
-/
noncomputable
/-
**Profinite.NobelingProof.GoodProducts.range_equiv_smaller** 是 Mathlib 中的一个定义，位于
命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：range_equiv_smaller (o : Ordinal) : range (π C (ord I · < o)) ≃ smaller C 
o
参数：o : Ordinal。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.GoodProducts.range_equiv_smaller_toFun_bijective
`：range_equiv_smaller_toFun_bijective (o : Ordinal) : Function.Bijective (range_
equiv_smaller_toFun C o)
-/
def range_equiv_smaller (o : Ordinal) : range (π C (ord I · < o)) ≃ smaller C o :=
  Equiv.ofBijective (range_equiv_smaller_toFun C o) (range_equiv_smaller_toFun_bijective C o)
/-
**Profinite.NobelingProof.GoodProducts.smaller_factorization** 是 Mathlib 中的一个定理，
位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：smaller_factorization (o : Ordinal) : (fun (p : smaller C o) => p.1) ∘ (ra
nge_equiv_smaller C o).toFun = (πs C o) ∘ (fun (p : range (π C (ord I · < o))) =
> p.1)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smaller_factorization (o : Ordinal) :
    (fun (p : smaller C o) ↦ p.1) ∘ (range_equiv_smaller C o).toFun =
    (πs C o) ∘ (fun (p : range (π C (ord I · < o))) ↦ p.1) := by rfl
/-
**Profinite.NobelingProof.GoodProducts.linearIndependent_iff_smaller** 是 Mathlib
 中的一个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：linearIndependent_iff_smaller (o : Ordinal) : LinearIndependent Int (GoodP
roducts.eval (π C (ord I · < o))) ↔ LinearIndependent Int (fun (p : smaller C o)
 => p.1)
参数：o : Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependent_iff_range`：linear
Independent_iff_range : LinearIndependent Int (GoodProducts.eval C) ↔ LinearInde
pendent Int (fun (p : range C) => p.1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.linearIndependent_iff`：∀ {ι : Type u'} {R : Type u_2} {M : Typ
e u_4} {M' : Type u_5} {v : ι → M} [inst : Ring R] [inst_1 : AddCommGroup M]   [
inst_2 : AddCommGroup…
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Profinite.NobelingProof.injective_πs`：injective_πs (o : Ordinal) : Funct
ion.Injective (πs C o)
· 使用定理 `Profinite.NobelingProof.GoodProducts.smaller_factorization`：smaller_fact
orization (o : Ordinal) : (fun (p : smaller C o) => p.1) ∘ (range_equiv_smaller 
C o).toFun = (πs C o) ∘ (fun (p : range (π C (or…
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
-/
theorem linearIndependent_iff_smaller (o : Ordinal) :
    LinearIndependent ℤ (GoodProducts.eval (π C (ord I · < o))) ↔
    LinearIndependent ℤ (fun (p : smaller C o) ↦ p.1) := by
  rw [GoodProducts.linearIndependent_iff_range,
    ← LinearMap.linearIndependent_iff (πs C o)
    (LinearMap.ker_eq_bot_of_injective (injective_πs _ _)), ← smaller_factorization C o]
  exact linearIndependent_equiv _
/-
**Profinite.NobelingProof.GoodProducts.smaller_mono** 是 Mathlib 中的一个定理，位于命名空间 `P
rofinite.NobelingProof.GoodProducts`。
形式化陈述：smaller_mono {o₁ o₂ : Ordinal} (h : o₁ <= o₂) : smaller C o₁ subseteq smal
ler C o₂
参数：h : o₁ <= o₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.Products.isGood_mono`：isGood_mono {l : Products 
I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (hl : l.isGood (π C (ord I · < o₁))) : l.isG
ood (π C (ord I · < o₂))
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.eval.eq_1`：∀ {I : Type u} (C : Set 
(I → Bool)) [inst : LinearOrder I] (l : { l // Profinite.NobelingProof.Products.
isGood C l }),   Profinite.NobelingP…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.Products.eval_πs'`：eval_πs' {l : Products I} {o₁
 o₂ : Ordinal} (h : o₁ <= o₂) (hlt : forall i in l.val, ord I i < o₁) : πs' C h 
(l.eval (π C (ord I · < o₁))) =…
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood`：prop_of_isGood {l : Pro
ducts I} (J : I -> Prop) [forall j, Decidable (J j)] (h : l.isGood (π C J)) : fo
rall a, a in l.val -> J a
· 使用定理 `LocallyConstant.coe_inj`：coe_inj {f g : LocallyConstant X Y} : (f : X ->
 Y) = g ↔ f = g
· 使用定理 `Profinite.NobelingProof.coe_πs`：coe_πs (o : Ordinal) (f : LocallyConstan
t (π C (ord I · < o)) Int) : πs C o f = f ∘ ProjRestrict C (ord I · < o)
· 使用定理 `LocallyConstant.toFun_eq_coe`：toFun_eq_coe (f : LocallyConstant X Y) : f
.toFun = f
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Profinite.NobelingProof.coe_πs'`：coe_πs' {o₁ o₂ : Ordinal} (h : o₁ <= o₂
) (f : LocallyConstant (π C (ord I · < o₁)) Int) : (πs' C h f).toFun = f.toFun ∘
 (ProjRestricts C (fu…
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Profinite.NobelingProof.projRestricts_comp_projRestrict`：projRestricts_c
omp_projRestrict (h : forall i, J i -> K i) : ProjRestricts C h ∘ ProjRestrict C
 K = ProjRestrict C J
-/
theorem smaller_mono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : smaller C o₁ ⊆ smaller C o₂ := by
  rintro f ⟨g, hg, rfl⟩
  simp only [smaller, Set.mem_image]
  use πs' C h g
  obtain ⟨⟨l, gl⟩, rfl⟩ := hg
  refine ⟨?_, ?_⟩
  · use ⟨l, Products.isGood_mono C h gl⟩
    ext x
    rw [eval, ← Products.eval_πs' _ h (Products.prop_of_isGood C _ gl), eval]
  · rw [← LocallyConstant.coe_inj, coe_πs C o₂, ← LocallyConstant.toFun_eq_coe, coe_πs',
      Function.comp_assoc, projRestricts_comp_projRestrict C _, coe_πs]
    rfl

end GoodProducts

variable {o : Ordinal} (ho : Order.IsSuccLimit o)
include ho

/-
**Profinite.NobelingProof.Products.limitOrdinal** 是 Mathlib 中的一个定理，位于命名空间 `Profi
nite.NobelingProof.Products`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellF
oundedLT I] {o : Ordinal.{u}},   Order.IsSuccLimit o →     ∀ (l : Profinite.Nobe
lingProof.Products I),       Profinite.NobelingProof.Products.isGood (Profinite.
NobelingProof.π C fun x => Profinite.NobelingProof.ord I x < o)           l ↔   
      ∃ o' < o,           Profinite.NobelingProof.Products.isGood             (P
rofinite.NobelingProof.π C fun x => Profinite.NobelingProof.ord I x < o') l
参数：C : Set (I → Bool)；l : Profinite.NobelingProof.Products I；Profinite.NobelingP
roof.π C fun x => Profinite.NobelingProof.ord I x < o；Profinite.NobelingProof.π 
C fun x => Profinite.NobelingProof.ord I x < o'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood`：prop_of_isGood {l : Pro
ducts I} (J : I -> Prop) [forall j, Decidable (J j)] (h : l.isGood (π C J)) : fo
rall a, a in l.val -> J a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Profinite.NobelingProof.Products.eval_πs_image'`：eval_πs_image' {l : Pro
ducts I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (hl : forall i in l.val, ord I i < o₁)
 : eval (π C (ord I · < o₂)) '' { m |…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.Products.eval_πs'`：eval_πs' {l : Products I} {o₁
 o₂ : Ordinal} (h : o₁ <= o₂) (hlt : forall i in l.val, ord I i < o₁) : πs' C h 
(l.eval (π C (ord I · < o₁))) =…
· 使用定理 `Submodule.apply_mem_span_image_iff_mem_span`：apply_mem_span_image_iff_me
m_span [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {x : M} {s : Set M} (hf : Fu
nction.Injective f) : f x in Subm…
· 使用定理 `Profinite.NobelingProof.injective_πs'`：injective_πs' {o₁ o₂ : Ordinal} (
h : o₁ <= o₂) : Function.Injective (πs' C h)
· 使用定理 `Profinite.NobelingProof.Products.isGood_mono`：isGood_mono {l : Products 
I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (hl : l.isGood (π C (ord I · < o₁))) : l.isG
ood (π C (ord I · < o₂))
-/
theorem Products.limitOrdinal (l : Products I) : l.isGood (π C (ord I · < o)) ↔
    ∃ (o' : Ordinal), o' < o ∧ l.isGood (π C (ord I · < o')) := by
  refine ⟨fun h ↦ ?_, fun ⟨o', ⟨ho', hl⟩⟩ ↦ isGood_mono C (le_of_lt ho') hl⟩
  use Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a))
  have hslt : Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a)) < o := by
    simp only [Finset.sup_lt_iff ho.bot_lt, List.mem_toFinset]
    exact fun b hb ↦ ho.succ_lt (prop_of_isGood C (ord I · < o) h b hb)
  refine ⟨hslt, fun he ↦ h ?_⟩
  have hlt : ∀ i ∈ l.val, ord I i < Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a)) := by
    intro i hi
    simp only [Finset.lt_sup_iff, List.mem_toFinset, Order.lt_succ_iff]
    exact ⟨i, hi, le_rfl⟩
  rwa [eval_πs_image' C (le_of_lt hslt) hlt, ← eval_πs' C (le_of_lt hslt) hlt,
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C _)]

variable (hsC : contained C o)
include hsC
/-
**Profinite.NobelingProof.GoodProducts.union** 是 Mathlib 中的一个定理，位于命名空间 `Profinit
e.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellF
oundedLT I] {o : Ordinal.{u}},   Order.IsSuccLimit o →     Profinite.NobelingPro
of.contained C o →       Profinite.NobelingProof.GoodProducts.range C = ⋃ e, Pro
finite.NobelingProof.GoodProducts.smaller C ↑e
参数：C : Set (I → Bool)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Profinite.NobelingProof.Products.limitOrdinal`：∀ {I : Type u} (C : Set (
I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}, 
  Order.IsSuccLimit o →     ∀ (l : …
· 使用定理 `Profinite.NobelingProof.contained_eq_proj`：contained_eq_proj (o : Ordina
l) (h : contained C o) : C = π C (ord I · < o)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Profinite.NobelingProof.Products.eval_πs`：eval_πs {l : Products I} {o : 
Ordinal} (hlt : forall i in l.val, ord I i < o) : πs C o (l.eval (π C (ord I · <
 o))) = l.eval C
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood`：prop_of_isGood {l : Pro
ducts I} (J : I -> Prop) [forall j, Decidable (J j)] (h : l.isGood (π C J)) : fo
rall a, a in l.val -> J a
· 使用定理 `Profinite.NobelingProof.Products.isGood_mono`：isGood_mono {l : Products 
I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (hl : l.isGood (π C (ord I · < o₁))) : l.isG
ood (π C (ord I · < o₂))
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem GoodProducts.union : range C = ⋃ (e : {o' // o' < o}), (smaller C e.val) := by
  ext p
  simp only [smaller, range, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := hp
    rw [contained_eq_proj C o hsC, Products.limitOrdinal C ho] at hl
    obtain ⟨o', ho'⟩ := hl
    refine ⟨o', ho'.1, eval (π C (ord I · < o')) ⟨l, ho'.2⟩, ⟨l, ho'.2, rfl⟩, ?_⟩
    exact Products.eval_πs C (Products.prop_of_isGood C _ ho'.2)
  · obtain ⟨o', h, _, ⟨l, hl, rfl⟩, rfl⟩ := hp
    refine ⟨l, ?_, (Products.eval_πs C (Products.prop_of_isGood  C _ hl)).symm⟩
    rw [contained_eq_proj C o hsC]
    exact Products.isGood_mono C (le_of_lt h) hl

/--
The image of the `GoodProducts` in `C` is equivalent to the union of `smaller C o'` over all
ordinals `o' < o`.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Profinite.NobelingProof.GoodProducts.range_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Pr
ofinite.NobelingProof.GoodProducts`。
形式化陈述：{I : Type u} →   (C : Set (I → Bool)) →     [inst : LinearOrder I] →      
 [inst_1 : WellFoundedLT I] →         {o : Ordinal.{u}} →           Order.IsSucc
Limit o →             Profinite.NobelingProof.contained C o →               ↑(Pr
ofinite.NobelingProof.GoodProducts.range C) ≃                 ↑(⋃ e, Profinite.N
obelingProof.GoodProducts.smaller C ↑e)
参数：C : Set (I → Bool)；Profinite.NobelingProof.GoodProducts.range C；⋃ e, Profinit
e.NobelingProof.GoodProducts.smaller C ↑e。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.GoodProducts.union`：∀ {I : Type u} (C : Set (I →
 Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}},   O
rder.IsSuccLimit o →     Profini…
-/
noncomputable def GoodProducts.range_equiv : range C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val) :=
  Equiv.setCongr (union C ho hsC)
/-
**Profinite.NobelingProof.GoodProducts.range_equiv_factorization** 是 Mathlib 中的一
个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellF
oundedLT I] {o : Ordinal.{u}}   (ho : Order.IsSuccLimit o) (hsC : Profinite.Nobe
lingProof.contained C o),   (fun p => ↑p) ∘ (Profinite.NobelingProof.GoodProduct
s.range_equiv C ho hsC).toFun = fun p => ↑p
参数：C : Set (I → Bool)；ho : Order.IsSuccLimit o；hsC : Profinite.NobelingProof.con
tained C o；fun p => ↑p；Profinite.NobelingProof.GoodProducts.range_equiv C ho hsC
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GoodProducts.range_equiv_factorization :
    (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) ∘ (range_equiv C ho hsC).toFun =
    (fun (p : range C) ↦ (p.1 : LocallyConstant C ℤ)) := rfl
/-
**Profinite.NobelingProof.GoodProducts.linearIndependent_iff_union_smaller** 是 M
athlib 中的一个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellF
oundedLT I] {o : Ordinal.{u}},   Order.IsSuccLimit o →     Profinite.NobelingPro
of.contained C o →       (LinearIndependent ℤ (Profinite.NobelingProof.GoodProdu
cts.eval C) ↔         LinearIndependent ℤ fun (p : ↑(⋃ e, Profinite.NobelingProo
f.GoodProducts.smaller C ↑e)) => ↑p)
参数：C : Set (I → Bool)；LinearIndependent ℤ (Profinite.NobelingProof.GoodProducts.
eval C) ↔         LinearIndependent ℤ fun (p : ↑(⋃ e, Profinite.NobelingProof.Go
odProducts.smaller C ↑e)) => ↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependent_iff_range`：linear
Independent_iff_range : LinearIndependent Int (GoodProducts.eval C) ↔ LinearInde
pendent Int (fun (p : range C) => p.1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.GoodProducts.range_equiv_factorization`：∀ {I : T
ype u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o
 : Ordinal.{u}}   (ho : Order.IsSuccLimit o) (hsC : …
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
-/
theorem GoodProducts.linearIndependent_iff_union_smaller :
    LinearIndependent ℤ (GoodProducts.eval C) ↔
      LinearIndependent ℤ (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) := by
  rw [GoodProducts.linearIndependent_iff_range, ← range_equiv_factorization C ho hsC]
  exact linearIndependent_equiv (range_equiv C ho hsC)

end Limit

end Profinite.NobelingProof

