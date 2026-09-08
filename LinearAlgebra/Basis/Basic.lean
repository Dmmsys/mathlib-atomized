/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Basic results on bases

The main goal of this file is to show the equivalence between bases and families of vectors that are
linearly independent and whose span is the whole space.

There are also various lemmas on bases on specific spaces (such as empty or singletons).

## Main results

* `Basis.linearIndependent`: the basis vectors are linear independent.
* `Basis.span_eq`: the basis vectors span the whole space.
* `Basis.mk`: construct a basis out of `v : ι → M` such that `LinearIndependent v` and
  `span (range v) = ⊤`.
-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module.Basis

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

section Properties

/-
**Module.Basis.repr_range** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_range : LinearMap.range (b.repr : M ->ₗ[R] ι ->₀ R) = Finsupp.support
ed R R univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `Finsupp.supported_univ`：supported_univ : supported M R (Set.univ : Set α
) = ⊤
-/
theorem repr_range : LinearMap.range (b.repr : M →ₗ[R] ι →₀ R) = Finsupp.supported R R univ := by
  rw [LinearEquiv.range, Finsupp.supported_univ]
/-
**Module.Basis.mem_span_repr_support** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mem_span_repr_support (m : M) : m in span R (b '' (b.repr m).support)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mem_span_repr_support (m : M) : m ∈ span R (b '' (b.repr m).support) :=
  (Finsupp.mem_span_image_iff_linearCombination _).2
    ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩
/-
**Module.Basis.repr_support_subset_of_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `Module
.Basis`。
形式化陈述：repr_support_subset_of_mem_span (s : Set ι) {m : M} (hm : m in span R (b '
' s)) : ↑(b.repr m).support subseteq s
参数：s : Set ι；hm : m in span R (b '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_linearCombination`：repr_linearCombination (v) : b.repr
 (Finsupp.linearCombination _ b v) = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mem_supported`：mem_supported {s : Set α} (p : α ->₀ M) : p in su
pported M R s ↔ ↑p.support subseteq s
-/
theorem repr_support_subset_of_mem_span (s : Set ι) {m : M}
    (hm : m ∈ span R (b '' s)) : ↑(b.repr m).support ⊆ s := by
  rcases (Finsupp.mem_span_image_iff_linearCombination _).1 hm with ⟨l, hl, rfl⟩
  rwa [repr_linearCombination, ← Finsupp.mem_supported R l]
/-
**Module.Basis.mem_span_image** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mem_span_image {m : M} {s : Set ι} : m in span R (b '' s) ↔ ↑(b.repr m).su
pport subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.repr_support_subset_of_mem_span`：repr_support_subset_of_mem
_span (s : Set ι) {m : M} (hm : m in span R (b '' s)) : ↑(b.repr m).support subs
eteq s
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Module.Basis.mem_span_repr_support`：mem_span_repr_support (m : M) : m in
 span R (b '' (b.repr m).support)
-/
theorem mem_span_image {m : M} {s : Set ι} : m ∈ span R (b '' s) ↔ ↑(b.repr m).support ⊆ s :=
  ⟨repr_support_subset_of_mem_span _ _, fun h ↦
    span_mono (Set.image_mono h) (mem_span_repr_support b _)⟩

@[simp]
/-
**Module.Basis.self_mem_span_image** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：self_mem_span_image [Nontrivial R] {i : ι} {s : Set ι} : b i in span R (b 
'' s) ↔ i in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem self_mem_span_image [Nontrivial R] {i : ι} {s : Set ι} :
    b i ∈ span R (b '' s) ↔ i ∈ s := by
  simp [mem_span_image, Finsupp.support_single]
/-
**Module.Basis.mem_span** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : Module.Basis ι R M) (x :
 M), x ∈ Submodule.span R (Set.range ⇑b)
参数：b : Module.Basis ι R M；x : M；Set.range ⇑b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Module.Basis.mem_span_repr_support`：mem_span_repr_support (m : M) : m in
 span R (b '' (b.repr m).support)
-/
protected theorem mem_span (x : M) : x ∈ span R (range b) :=
  span_mono (image_subset_range _ _) (mem_span_repr_support b x)

@[simp]
/-
**Module.Basis.span_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : Module.Basis ι R M), Sub
module.span R (Set.range ⇑b) = ⊤
参数：b : Module.Basis ι R M；Set.range ⇑b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Module.Basis.mem_span`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b :
 Module.Bas…
-/
protected theorem span_eq : span R (range b) = ⊤ :=
  eq_top_iff.mpr fun x _ => b.mem_span x
/-
**Module.Basis._root_.Submodule.eq_top_iff_forall_basis_mem** 是 Mathlib 中的一个定理，位
于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.eq_top_iff_forall_basis_mem {p : Submodule R M} :
    p = ⊤ ↔ ∀ i, b i ∈ p := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  replace h : range b ⊆ p := by rintro - ⟨i, rfl⟩; exact h i
  simpa using span_mono (R := R) h
/-
**Module.Basis.index_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：index_nonempty (b : Basis ι R M) [Nontrivial M] : Nonempty ι
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.ext_elem_iff`：ext_elem_iff {x y : M} : x = y ↔ forall i, b.
repr x i = b.repr y i
-/
theorem index_nonempty (b : Basis ι R M) [Nontrivial M] : Nonempty ι := by
  obtain ⟨x, y, ne⟩ : ∃ x y : M, x ≠ y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem_iff.2 ne)
  exact ⟨i⟩
/-
**Module.Basis.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : Module.Basis ι R M), Lin
earIndependent R ⇑b
参数：b : Module.Basis ι R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.repr_linearCombination`：repr_linearCombination (v) : b.repr
 (Finsupp.linearCombination _ b v) = v
-/
protected theorem linearIndependent : LinearIndependent R b :=
  fun x y hxy => by
    rw [← b.repr_linearCombination x, hxy, b.repr_linearCombination y]
/-
**Module.Basis.linearIndepOn** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : Module.Basis ι R M) (s :
 Set ι), LinearIndepOn R (⇑b) s
参数：b : Module.Basis ι R M；s : Set ι；⇑b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndependent.linearIndepOn`：LinearIndependent.linearIndepOn (h : Li
nearIndependent R v) (s : Set ι) : LinearIndepOn R v s
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
protected lemma linearIndepOn (s : Set ι) : LinearIndepOn R b s :=
  b.linearIndependent.linearIndepOn s
/-
**Module.Basis.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : Module.Basis ι R M) [Non
trivial R] (i : ι), b i ≠ 0
参数：b : Module.Basis ι R M；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=
  b.linearIndependent.ne_zero i
/-
**Module.Basis.injective_constr_of_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `
Module.Basis`。
形式化陈述：injective_constr_of_linearIndependent [Semiring R₂] [Module R₂ M'] [SMulCo
mmClass R R₂ M'] {v : ι -> M'} (hv : LinearIndependent R v) : Injective (b.const
r R₂ v)
参数：hv : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `LinearIndependent.finsuppLinearCombination_injective`：∀ {ι : Type u'} {R
 : Type u_2} {M : Type u_4} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMon
oid M]   [inst_2 : _root_.Module R M], Lin…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.linearCombination_mapDomain`：linearCombination_mapDomain (f : α 
-> α') (l : α ->₀ R) : (linearCombination R v') (mapDomain f l) = (linearCombina
tion R (v' ∘ f)) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
-/
theorem injective_constr_of_linearIndependent
    [Semiring R₂] [Module R₂ M'] [SMulCommClass R R₂ M'] {v : ι → M'}
    (hv : LinearIndependent R v) : Injective (b.constr R₂ v) :=
  fun _ _ hab ↦ b.repr.injective <| hv.finsuppLinearCombination_injective <| by
    simpa [constr_def] using hab

end Properties

variable {v : ι → M} {x y : M}

section Mk

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

/-- A linear independent family of vectors spanning the whole module is a basis. -/
/-
**Module.Basis.mk** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     {M : Type u_5} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             {v : ι → M} → LinearIndependent R v → ⊤ ≤ Submodule.span R 
(Set.range v) → Module.Basis ι R M
参数：Set.range v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear independent family of vectors spanning the whole module is a basis.
-/
protected noncomputable def mk : Basis ι R M :=
  .ofRepr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
      invFun := Finsupp.linearCombination _ v
      left_inv := fun x => hli.linearCombination_repr ⟨x, _⟩
      right_inv := fun _ => hli.repr_eq rfl }

@[simp]
/-
**Module.Basis.mk_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ :=
  rfl
/-
**Module.Basis.mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mk_apply (i : ι) : Basis.mk hli hsp i = v i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
  show Finsupp.linearCombination _ v _ = v i by simp

@[simp]
/-
**Module.Basis.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_mk : ⇑(Basis.mk hli hsp) = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
-/
theorem coe_mk : ⇑(Basis.mk hli hsp) = v :=
  funext (mk_apply _ _)

end Mk

section Coord

@[simp]
/-
**Module.Basis.linearIndependent_coord** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：linearIndependent_coord {R : Type*} [CommSemiring R] [Module R M] (b : Bas
is ι R M) : LinearIndependent R b.coord
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `linearIndependent_iff'ₛ`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {
v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M],   L…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem linearIndependent_coord {R : Type*} [CommSemiring R] [Module R M] (b : Basis ι R M) :
    LinearIndependent R b.coord := by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s l₁ l₂ h j hj ↦ ?_
  simpa [hj, Finsupp.single_apply] using congr($h (b j))

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

variable {hli hsp}

/-- Given a basis, the `i`th element of the dual basis evaluates to 1 on the `i`th element of the
basis. -/
/-
**Module.Basis.mk_coord_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).coord i (v i) = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.repr_eq_single`：LinearIndependent.repr_eq_single (i) (
x : span R (range v)) (hx : ↑x = v i) : hv.repr x = Finsupp.single i 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b

--- 原说明 ---
Given a basis, the `i`th element of the dual basis evaluates to 1 on the `i`th e
lement of the
basis.
-/
theorem mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).coord i (v i) = 1 :=
  show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]

/-- Given a basis, the `i`th element of the dual basis evaluates to 0 on the `j`th element of the
basis if `j ≠ i`. -/
/-
**Module.Basis.mk_coord_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mk_coord_apply_ne {i j : ι} (h : j != i) : (Basis.mk hli hsp).coord i (v j
) = 0
参数：h : j != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.repr_eq_single`：LinearIndependent.repr_eq_single (i) (
x : span R (range v)) (hx : ↑x = v i) : hv.repr x = Finsupp.single i 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Given a basis, the `i`th element of the dual basis evaluates to 0 on the `j`th e
lement of the
basis if `j ≠ i`.
-/
theorem mk_coord_apply_ne {i j : ι} (h : j ≠ i) : (Basis.mk hli hsp).coord i (v j) = 0 :=
  show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]

/-- Given a basis, the `i`th element of the dual basis evaluates to the Kronecker delta on the
`j`th element of the basis. -/
/-
**Module.Basis.mk_coord_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mk_coord_apply [DecidableEq ι] {i j : ι} : (Basis.mk hli hsp).coord i (v j
) = if j = i then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.mk_coord_apply_eq`：mk_coord_apply_eq (i : ι) : (Basis.mk hl
i hsp).coord i (v i) = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Module.Basis.mk_coord_apply_ne`：mk_coord_apply_ne {i j : ι} (h : j != i)
 : (Basis.mk hli hsp).coord i (v j) = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e

--- 原说明 ---
Given a basis, the `i`th element of the dual basis evaluates to the Kronecker de
lta on the
`j`th element of the basis.
-/
theorem mk_coord_apply [DecidableEq ι] {i j : ι} :
    (Basis.mk hli hsp).coord i (v j) = if j = i then 1 else 0 := by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]

end Coord

section Span

variable (hli : LinearIndependent R v)

/-- A linear independent family of vectors is a basis for their span. -/
/-
**Module.Basis.span** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     {M : Type u_5} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             {v : ι → M} → LinearIndependent R v → Module.Basis ι R ↥(Su
bmodule.span R (Set.range v))
参数：Submodule.span R (Set.range v)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_span`：linearIndependent_span (hs : LinearIndependent R
 v) : LinearIndependent R (M

--- 原说明 ---
A linear independent family of vectors is a basis for their span.
-/
protected noncomputable def span : Basis ι R (span R (range v)) :=
  Basis.mk (linearIndependent_span hli) <| by
    intro x _
    have : ∀ i, v i ∈ span R (range v) := fun i ↦ subset_span (Set.mem_range_self _)
    have h₁ : (((↑) : span R (range v) → M) '' range fun i => ⟨v i, this i⟩) = range v := by
      simp only [← Set.range_comp]
      rfl
    have h₂ : map (Submodule.subtype (span R (range v))) (span R (range fun i => ⟨v i, this i⟩)) =
        span R (range v) := by
      rw [← span_image, Submodule.coe_subtype, h₁]
    have h₃ : (x : M) ∈ map (Submodule.subtype (span R (range v)))
        (span R (Set.range fun i => Subtype.mk (v i) (this i))) := by
      rw [h₂]
      apply Subtype.mem x
    rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩
    have h_x_eq_y : x = y := by
      rw [Subtype.ext_iff, ← hy₂]
      simp
    rwa [h_x_eq_y]

@[simp]
/-
**Module.Basis.span_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v : ι → M} (hli : LinearInde
pendent R v) (i : ι), (Module.Basis.span hli) i = ⟨v i, ⋯⟩
参数：hli : LinearIndependent R v；i : ι；Module.Basis.span hli。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
· 使用定理 `linearIndependent_span`：linearIndependent_span (hs : LinearIndependent R
 v) : LinearIndependent R (M
-/
protected theorem span_apply (i : ι) :
    Basis.span hli i = ⟨v i, Submodule.subset_span <| mem_range_self _⟩ := by
  ext
  exact congr_arg ((↑) : span R (range v) → M) <| Basis.mk_apply _ _ _
/-
**Module.Basis.coe_span_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v : ι → M} (hli : LinearInde
pendent R v) (i : ι), ↑((Module.Basis.span hli) i) = v i
参数：hli : LinearIndependent R v；i : ι；(Module.Basis.span hli) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Module.Basis.span_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v
 : ι → M} (hl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem coe_span_apply (i : ι) : (Basis.span hli i : M) = v i := by simp

@[simp]
/-
**Module.Basis.span_repr_eq_single** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v : ι → M} (hli : LinearInde
pendent R v) (i : ι)   (hi : optParam (v i ∈ Submodule.span R (Set.range v)) ⋯),
 (Module.Basis.span hli).repr ⟨v i, hi⟩ = fun₀ | i => 1
参数：hli : LinearIndependent R v；i : ι；hi : optParam (v i ∈ Submodule.span R (Set.
range v)) ⋯；Module.Basis.span hli。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `linearIndependent_span`：linearIndependent_span (hs : LinearIndependent R
 v) : LinearIndependent R (M
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem span_repr_eq_single (i : ι)
    (hi : v i ∈ span R (range v) := subset_span <| mem_range_self i) :
    (Basis.span hli).repr ⟨v i, hi⟩ = single i 1 := by
  rw [← LinearEquiv.eq_symm_apply]
  simp [Basis.span]
/-
**Module.Basis.span_neg** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`。
形式化陈述：span_neg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {v : ι -> M}
 (hli : LinearIndependent R v) (h : span R (range v) = span R (range (-v))
参数：hli : LinearIndependent R v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `LinearIndependent.neg`：LinearIndependent.neg (hv : LinearIndependent R v
) : LinearIndependent R (-v)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Module.Basis.span_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v
 : ι → M} (hl…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma span_neg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {v : ι → M} (hli : LinearIndependent R v)
    (h : span R (range v) = span R (range (-v)) := by simp [← neg_range']) :
    Basis.span hli.neg = ((Basis.span hli).map <| (LinearEquiv.neg _).trans (.ofEq _ _ h)) := by
  ext; simp

end Span

set_option backward.isDefEq.respectTransparency false in
/-- Any basis is a maximal linear independent set.
-/
/-
**Module.Basis.maximal** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：maximal [Nontrivial R] (b : Basis ι R M) : b.linearIndependent.Maximal
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
· 使用定理 `LinearIndependent.linearCombination_ne_of_notMem_support`：LinearIndepend
ent.linearCombination_ne_of_notMem_support [Nontrivial R] (hv : LinearIndependen
t R v) {x : ι} (f : ι ->₀ R) (h : x ∉ f.suppor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum_embDomain`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] {v : α →₀ M}   {f : α ↪
 β} {g : β …

--- 原说明 ---
Any basis is a maximal linear independent set.
-/
theorem maximal [Nontrivial R] (b : Basis ι R M) : b.linearIndependent.Maximal := fun w hi h => by
  -- If `w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.linearCombination_repr x
  -- This then expresses `x` as a linear combination
  -- of elements of `w` which are in the range of `b`,
  let u : ι ↪ w :=
    ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
      b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
  simp_rw [Finsupp.linearCombination_apply] at e
  change ((b.repr x).sum fun (i : ι) (a : R) ↦ a • (u i : M)) = ((⟨x, p⟩ : w) : M) at e
  rw [← Finsupp.sum_embDomain (f := u) (g := fun x r ↦ r • (x : M)),
      ← Finsupp.linearCombination_apply] at e
  -- Now we can contradict the linear independence of `hi`
  refine hi.linearCombination_ne_of_notMem_support _ ?_ e
  simp only [Finset.mem_map, Finsupp.support_embDomain]
  rintro ⟨j, -, W⟩
  simp only [u, Embedding.coeFn_mk, Subtype.mk_eq_mk] at W
  apply q ⟨j, W⟩
/-
**Module.Basis.uniqueBasis** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
形式化陈述：uniqueBasis [Subsingleton R] : Unique (Basis ι R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueBasis [Subsingleton R] : Unique (Basis ι R M) :=
  ⟨⟨⟨default⟩⟩, fun ⟨b⟩ => by rw [Subsingleton.elim b]⟩

variable (b : Basis ι R M)

section Singleton

/-- `Basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. -/
/-
**Module.Basis.singleton** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：(ι : Type u_7) → (R : Type u_8) → [Unique ι] → [inst : Semiring R] → Modul
e.Basis ι R R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`.
-/
protected def singleton (ι R : Type*) [Unique ι] [Semiring R] : Basis ι R R :=
  ofRepr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Module.Basis.singleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：singleton_apply (ι R : Type*) [Unique ι] [Semiring R] (i) : Basis.singleto
n ι R i = 1
参数：ι R : Type*；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_apply (ι R : Type*) [Unique ι] [Semiring R] (i) : Basis.singleton ι R i = 1 :=
  apply_eq_iff.mpr (by simp [Basis.singleton])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Module.Basis.singleton_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：singleton_repr (ι R : Type*) [Unique ι] [Semiring R] (x i) : (Basis.single
ton ι R).repr x i = x
参数：ι R : Type*；x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_repr (ι R : Type*) [Unique ι] [Semiring R] (x i) :
    (Basis.singleton ι R).repr x i = x := by simp [Basis.singleton, Unique.eq_default i]

@[simp]
/-
**Module.Basis.coe_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_singleton {ι R : Type*} [Unique ι] [Semiring R] : ⇑(Basis.singleton ι 
R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.singleton_apply`：singleton_apply (ι R : Type*) [Unique ι] [
Semiring R] (i) : Basis.singleton ι R i = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_singleton {ι R : Type*} [Unique ι] [Semiring R] :
    ⇑(Basis.singleton ι R) = 1 := by
  ext; simp

end Singleton

section Empty

variable (M)

/-- If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis for `M`. -/
/-
**Module.Basis.empty** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     (M : Type u_5) →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → [
Subsingleton M] → [IsEmpty ι] → Module.Basis ι R M
参数：M : Type u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis 
for `M`.
-/
protected def empty [Subsingleton M] [IsEmpty ι] : Basis ι R M :=
  ofRepr 0
/-
**Module.Basis.emptyUnique** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
形式化陈述：emptyUnique [Subsingleton M] [IsEmpty ι] : Unique (Basis ι R M) where defa
ult
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance emptyUnique [Subsingleton M] [IsEmpty ι] : Unique (Basis ι R M) where
  default := Basis.empty M
  uniq := fun _ => congr_arg ofRepr <| Subsingleton.elim _ _

end Empty

section Module.IsTorsionFree

set_option backward.isDefEq.respectTransparency false in
-- Can't be an instance because the basis can't be inferred.
/-
**Module.Basis.isTorsionFree** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : Module.Basis ι R M), Mod
ule.IsTorsionFree R M
参数：b : Module.Basis ι R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.moduleIsTorsionFree`：Function.Injective.moduleIsTorsi
onFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective) (smul : forall (r : R
) (m : M), f (r • m) = r • f…
· 使用定理 `instIsTorsionFree`：∀ {R : Type u_1} [inst : Semiring R], Module.IsTorsio
nFree R R
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma isTorsionFree (b : Basis ι R M) :
    Module.IsTorsionFree R M := b.repr.injective.moduleIsTorsionFree _ (by simp)
/-
**Module.Basis.smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [IsDomain R] (b : Module.Basi
s ι R M) {c : R} {x : M}, c • x = 0 ↔ c = 0 ∨ x = 0
参数：b : Module.Basis ι R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.isTorsionFree`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_
5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 (b : Module.Bas…
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
protected theorem smul_eq_zero [IsDomain R] (b : Basis ι R M) {c : R} {x : M} :
    c • x = 0 ↔ c = 0 ∨ x = 0 := by have := b.isTorsionFree; exact smul_eq_zero

end Module.IsTorsionFree

section Singleton

/-
**Module.Basis.basis_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：basis_singleton_iff {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [
Module R M] [IsTorsionFree R M] (ι : Type*) [Unique ι] : Nonempty (Basis ι R M) 
↔ exists x != 0, forall y : M, exists r : R, r • x = y
参数：ι : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_unique`：range_unique [Unique ι] : range f = {f default}
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Finsupp.unique_ext`：unique_ext [Unique α] {f g : α ->₀ M} (h : f default
 = g default) : f = g
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem basis_singleton_iff {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsTorsionFree R M] (ι : Type*) [Unique ι] :
    Nonempty (Basis ι R M) ↔ ∃ x ≠ 0, ∀ y : M, ∃ r : R, r • x = y := by
  constructor
  · rintro ⟨b⟩
    refine ⟨b default, b.linearIndependent.ne_zero _, ?_⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
    refine ⟨ofRepr <| LinearEquiv.symm
      { toFun := fun f => f default • x
        invFun := fun y => Finsupp.single default (w y).choose
        left_inv := fun f => Finsupp.unique_ext ?_
        right_inv := fun y => ?_
        map_add' := fun y z => ?_
        map_smul' := fun c y => ?_ }⟩
    · simp [Finsupp.add_apply, add_smul]
    · simp only [Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [← smul_assoc]
    · refine smul_left_injective _ nz ?_
      simp only [Finsupp.single_eq_same]
      exact (w (f default • x)).choose_spec
    · simp only [Finsupp.single_eq_same]
      exact (w y).choose_spec

end Singleton
end Basis

open Fintype in
/-
**Module.card_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Fintype ι] (b : Mod
ule.Basis ι R M) [inst : Fintype R] [inst_4 : Fintype M],   Fintype.card M = Fin
type.card R ^ Fintype.card ι
参数：b : Module.Basis ι R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_fintype [Semiring R] [AddCommMonoid M] [Module R M] [Fintype ι] (b : Basis ι R M)
    [Fintype R] [Fintype M] :
    card M = card R ^ card ι := by
  classical
    calc
      card M = card (ι → R) := card_congr b.equivFun.toEquiv
      _ = card R ^ card ι := by simp

end Module

