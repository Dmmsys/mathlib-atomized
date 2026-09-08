/-
Copyright (c) 2024 Gabin Kolly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly, David Wärn
-/
module

public import Mathlib.ModelTheory.DirectLimit
public import Mathlib.Order.Ideal

/-!
# Partial Isomorphisms

This file defines partial isomorphisms between first-order structures.

## Main Definitions
- `FirstOrder.Language.PartialEquiv` is defined so that `L.PartialEquiv M N`, annotated
  `M ≃ₚ[L] N`, is the type of equivalences between substructures of `M` and `N`. These can be
  ordered, with an order that is defined here in terms of a commutative square, but could also be
  defined as the order on the graphs of the partial equivalences under inclusion as subsets of
  `M × N`.
- `FirstOrder.Language.FGEquiv` is the type of partial equivalences `M ≃ₚ[L] N` with
  finitely-generated domain (or equivalently, codomain).
- `FirstOrder.Language.IsExtensionPair` is defined so that `L.IsExtensionPair M N` indicates that
  any finitely-generated partial equivalence from `M` to `N` can be extended to include an arbitrary
  element `m : M` in its domain.

## Main Results
- `FirstOrder.Language.embedding_from_cg` shows that if structures `M` and `N` form an equivalence
  pair with `M` countably-generated, then any finite-generated partial equivalence between them
  can be extended to an embedding `M ↪[L] N`.
- `FirstOrder.Language.equiv_from_cg` shows that if countably-generated structures `M` and `N` form
  an equivalence pair in both directions, then any finite-generated partial equivalence between them
  can be extended to an isomorphism `M ↪[L] N`.
- The proofs of these results are adapted in part from David Wärn's approach to countable dense
  linear orders, a special case of this phenomenon in the case where `L = Language.order`.

-/

@[expose] public section

universe u v w w'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) (M : Type w) (N : Type w')
variable [L.Structure M] [L.Structure N]

open FirstOrder Structure Substructure

/-- A partial `L`-equivalence, implemented as an equivalence between substructures. -/
/-
**FirstOrder.Language.PartialEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：(L : FirstOrder.Language) → (M : Type w) → (N : Type w') → [L.Structure M]
 → [L.Structure N] → Type (max w w')
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial `L`-equivalence, implemented as an equivalence between substructures.
-/
structure PartialEquiv where
  /-- The substructure which is the domain of the equivalence. -/
  dom : L.Substructure M
  /-- The substructure which is the codomain of the equivalence. -/
  cod : L.Substructure N
  /-- The equivalence between the two subdomains. -/
  toEquiv : dom ≃[L] cod

@[inherit_doc]
scoped[FirstOrder] notation:25 M " ≃ₚ[" L "] " N =>
  FirstOrder.Language.PartialEquiv L M N

variable {L M N}

namespace PartialEquiv

/-
**FirstOrder.Language.PartialEquiv.instInhabited_self** 是 Mathlib 中的一个实例，位于命名空间 
`FirstOrder.Language.PartialEquiv`。
形式化陈述：instInhabited_self : Inhabited (M ≃ₚ[L] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instInhabited_self : Inhabited (M ≃ₚ[L] M) :=
  ⟨⊤, ⊤, Equiv.refl L (⊤ : L.Substructure M)⟩

/-- Maps to the symmetric partial equivalence. -/
/-
**FirstOrder.Language.PartialEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.PartialEquiv`。
形式化陈述：symm (f : M ≃ₚ[L] N) : N ≃ₚ[L] M where dom
参数：f : M ≃ₚ[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps to the symmetric partial equivalence.
-/
def symm (f : M ≃ₚ[L] N) : N ≃ₚ[L] M where
  dom := f.cod
  cod := f.dom
  toEquiv := f.toEquiv.symm

@[simp]
/-
**FirstOrder.Language.PartialEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.PartialEquiv`。
形式化陈述：symm_symm (f : M ≃ₚ[L] N) : f.symm.symm = f
参数：f : M ≃ₚ[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (f : M ≃ₚ[L] N) : f.symm.symm = f :=
  rfl
/-
**FirstOrder.Language.PartialEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.PartialEquiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (M ≃ₚ[L] N) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `FirstOrder.Language.PartialEquiv.symm_symm`：symm_symm (f : M ≃ₚ[L] N) : 
f.symm.symm = f
-/
theorem symm_bijective : Function.Bijective (symm : (M ≃ₚ[L] N) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**FirstOrder.Language.PartialEquiv.symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.PartialEquiv`。
形式化陈述：symm_apply (f : M ≃ₚ[L] N) (x : f.cod) : f.symm.toEquiv x = f.toEquiv.symm
 x
参数：f : M ≃ₚ[L] N；x : f.cod。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_apply (f : M ≃ₚ[L] N) (x : f.cod) : f.symm.toEquiv x = f.toEquiv.symm x :=
  rfl
/-
**FirstOrder.Language.PartialEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langua
ge.PartialEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (M ≃ₚ[L] N) :=
  ⟨fun f g ↦ ∃ h : f.dom ≤ g.dom,
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.toEquiv.toEmbedding⟩
/-
**FirstOrder.Language.PartialEquiv.le_def** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.PartialEquiv`。
形式化陈述：le_def (f g : M ≃ₚ[L] N) : f <= g ↔ exists h : f.dom <= g.dom, (subtype _)
.comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) = (subtype _).comp
 f.toEquiv.toEmbedding
参数：f g : M ≃ₚ[L] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def (f g : M ≃ₚ[L] N) : f ≤ g ↔ ∃ h : f.dom ≤ g.dom,
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.toEquiv.toEmbedding :=
  Iff.rfl
/-
**FirstOrder.Language.PartialEquiv.dom_le_dom** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.PartialEquiv`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} {N : Type w'} [inst : L.Structure
 M] [inst_1 : L.Structure N]   {f g : L.PartialEquiv M N}, f ≤ g → f.dom ≤ g.dom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] theorem dom_le_dom {f g : M ≃ₚ[L] N} : f ≤ g → f.dom ≤ g.dom := fun ⟨le, _⟩ ↦ le
/-
**FirstOrder.Language.PartialEquiv.cod_le_cod** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.PartialEquiv`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} {N : Type w'} [inst : L.Structure
 M] [inst_1 : L.Structure N]   {f g : L.PartialEquiv M N}, f ≤ g → f.cod ≤ g.cod
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Equiv.apply_symm_apply`：apply_symm_apply (f : M ≃[L]
 N) (a : N) : f (f.symm a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[gcongr] theorem cod_le_cod {f g : M ≃ₚ[L] N} : f ≤ g → f.cod ≤ g.cod := by
  rintro ⟨_, eq_fun⟩ n hn
  let m := f.toEquiv.symm ⟨n, hn⟩
  have : ((subtype _).comp f.toEquiv.toEmbedding) m = n := by simp only [m, Embedding.comp_apply,
    Equiv.coe_toEmbedding, Equiv.apply_symm_apply, coe_subtype]
  rw [← this, ← eq_fun]
  simp only [Embedding.comp_apply, coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
    SetLike.coe_mem]
/-
**FirstOrder.Language.PartialEquiv.subtype_toEquiv_inclusion** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.PartialEquiv`。
形式化陈述：subtype_toEquiv_inclusion {f g : M ≃ₚ[L] N} (h : f <= g) : (subtype _).com
p (g.toEquiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h))) = (subtyp
e _).comp f.toEquiv.toEmbedding
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
-/
theorem subtype_toEquiv_inclusion {f g : M ≃ₚ[L] N} (h : f ≤ g) :
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h))) =
      (subtype _).comp f.toEquiv.toEmbedding := by
  let ⟨_, eq⟩ := h; exact eq
/-
**FirstOrder.Language.PartialEquiv.toEquiv_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.PartialEquiv`。
形式化陈述：toEquiv_inclusion {f g : M ≃ₚ[L] N} (h : f <= g) : g.toEquiv.toEmbedding.c
omp (Substructure.inclusion (dom_le_dom h)) = (Substructure.inclusion (cod_le_co
d h)).comp f.toEquiv.toEmbedding
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `FirstOrder.Language.PartialEquiv.cod_le_cod`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Embedding.comp_inj`：comp_inj (h : N ↪[L] P) (f g : M
 ↪[L] N) : h.comp f = h.comp g ↔ f = g
· 使用定理 `FirstOrder.Language.PartialEquiv.subtype_toEquiv_inclusion`：subtype_toEq
uiv_inclusion {f g : M ≃ₚ[L] N} (h : f <= g) : (subtype _).comp (g.toEquiv.toEmb
edding.comp (Substructure.inclusion (dom_le_dom …
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toEquiv_inclusion {f g : M ≃ₚ[L] N} (h : f ≤ g) :
    g.toEquiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h)) =
      (Substructure.inclusion (cod_le_cod h)).comp f.toEquiv.toEmbedding := by
  rw [← (subtype _).comp_inj, subtype_toEquiv_inclusion h]
  ext
  simp
/-
**FirstOrder.Language.PartialEquiv.toEquiv_inclusion_apply** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.PartialEquiv`。
形式化陈述：toEquiv_inclusion_apply {f g : M ≃ₚ[L] N} (h : f <= g) (x : f.dom) : g.toE
quiv (Substructure.inclusion (dom_le_dom h) x) = Substructure.inclusion (cod_le_
cod h) (f.toEquiv x)
参数：h : f <= g；x : f.dom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.injective`：injective (f : M ↪[L] N) : Func
tion.Injective f
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `FirstOrder.Language.PartialEquiv.cod_le_cod`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.PartialEquiv.subtype_toEquiv_inclusion`：subtype_toEq
uiv_inclusion {f g : M ≃ₚ[L] N} (h : f <= g) : (subtype _).comp (g.toEquiv.toEmb
edding.comp (Substructure.inclusion (dom_le_dom …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toEquiv_inclusion_apply {f g : M ≃ₚ[L] N} (h : f ≤ g) (x : f.dom) :
    g.toEquiv (Substructure.inclusion (dom_le_dom h) x) =
      Substructure.inclusion (cod_le_cod h) (f.toEquiv x) := by
  apply (subtype _).injective
  change (subtype _).comp (g.toEquiv.toEmbedding.comp (inclusion _)) x = _
  rw [subtype_toEquiv_inclusion h]
  simp
/-
**FirstOrder.Language.PartialEquiv.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.PartialEquiv`。
形式化陈述：le_iff {f g : M ≃ₚ[L] N} : f <= g ↔ exists dom_le_dom : f.dom <= g.dom, ex
ists cod_le_cod : f.cod <= g.cod, forall x, inclusion cod_le_cod (f.toEquiv x) =
 g.toEquiv (inclusion dom_le_dom x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `FirstOrder.Language.PartialEquiv.cod_le_cod`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.PartialEquiv.toEquiv_inclusion_apply`：toEquiv_inclus
ion_apply {f g : M ≃ₚ[L] N} (h : f <= g) (x : f.dom) : g.toEquiv (Substructure.i
nclusion (dom_le_dom h) x) = Substructure.incl…
· 使用定理 `FirstOrder.Language.PartialEquiv.le_def`：le_def (f g : M ≃ₚ[L] N) : f <=
 g ↔ exists h : f.dom <= g.dom, (subtype _).comp (g.toEquiv.toEmbedding.comp (Su
bstructure.inclusion h)) = (s…
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_iff {f g : M ≃ₚ[L] N} : f ≤ g ↔
    ∃ dom_le_dom : f.dom ≤ g.dom,
    ∃ cod_le_cod : f.cod ≤ g.cod,
    ∀ x, inclusion cod_le_cod (f.toEquiv x) = g.toEquiv (inclusion dom_le_dom x) := by
  constructor
  · exact fun h ↦ ⟨dom_le_dom h, cod_le_cod h,
      by intro x; apply (subtype _).inj'; rwa [toEquiv_inclusion_apply]⟩
  · rintro ⟨dom_le_dom, le_cod, h_eq⟩
    rw [le_def]
    exact ⟨dom_le_dom, by ext; change subtype _ (g.toEquiv _) = _; rw [← h_eq]; rfl⟩

-- probably the initial design intended this to be private, just like `le_refl` and `le_antisymm`?
/-
**FirstOrder.Language.PartialEquiv.le_trans** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.PartialEquiv`。
形式化陈述：le_trans (f g h : M ≃ₚ[L] N) : f <= g -> g <= h -> f <= h
参数：f g h : M ≃ₚ[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Embedding.comp_assoc`：comp_assoc (f : M ↪[L] N) (g :
 N ↪[L] P) (h : P ↪[L] Q) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_trans (f g h : M ≃ₚ[L] N) : f ≤ g → g ≤ h → f ≤ h := by
  rintro ⟨le_fg, eq_fg⟩ ⟨le_gh, eq_gh⟩
  refine ⟨le_fg.trans le_gh, ?_⟩
  rw [← eq_fg, ← Embedding.comp_assoc (g := g.toEquiv.toEmbedding), ← eq_gh]
  ext
  simp
/-
**FirstOrder.Language.PartialEquiv.le_refl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.PartialEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_refl (f : M ≃ₚ[L] N) : f ≤ f := ⟨le_rfl, rfl⟩
/-
**FirstOrder.Language.PartialEquiv.le_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.PartialEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_antisymm (f g : M ≃ₚ[L] N) (le_fg : f ≤ g) (le_gf : g ≤ f) : f = g := by
  let ⟨dom_f, cod_f, equiv_f⟩ := f
  cases _root_.le_antisymm (dom_le_dom le_fg) (dom_le_dom le_gf)
  cases _root_.le_antisymm (cod_le_cod le_fg) (cod_le_cod le_gf)
  convert! rfl
  exact Equiv.injective_toEmbedding ((subtype _).comp_injective (subtype_toEquiv_inclusion le_fg))
/-
**FirstOrder.Language.PartialEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langua
ge.PartialEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (M ≃ₚ[L] N) where
  le_refl := private le_refl
  le_trans := le_trans
  le_antisymm := private le_antisymm

set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Language.PartialEquiv.symm_le_symm** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.PartialEquiv`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} {N : Type w'} [inst : L.Structure
 M] [inst_1 : L.Structure N]   {f g : L.PartialEquiv M N}, f ≤ g → f.symm ≤ g.sy
mm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.PartialEquiv.le_iff`：le_iff {f g : M ≃ₚ[L] N} : f <=
 g ↔ exists dom_le_dom : f.dom <= g.dom, exists cod_le_cod : f.cod <= g.cod, for
all x, inclusion cod_le_cod (…
· 使用定理 `FirstOrder.Language.PartialEquiv.cod_le_cod`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `FirstOrder.Language.Equiv.injective`：injective (f : M ≃[L] N) : Function
.Injective f
· 使用定理 `FirstOrder.Language.Equiv.apply_symm_apply`：apply_symm_apply (f : M ≃[L]
 N) (a : N) : f (f.symm a) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Equiv.symm_apply_apply`：symm_apply_apply (f : M ≃[L]
 N) (a : M) : f.symm (f a) = a
· 使用定理 `FirstOrder.Language.PartialEquiv.toEquiv_inclusion_apply`：toEquiv_inclus
ion_apply {f g : M ≃ₚ[L] N} (h : f <= g) (x : f.dom) : g.toEquiv (Substructure.i
nclusion (dom_le_dom h) x) = Substructure.incl…
-/
@[gcongr] lemma symm_le_symm {f g : M ≃ₚ[L] N} (hfg : f ≤ g) : f.symm ≤ g.symm := by
  rw [le_iff]
  refine ⟨cod_le_cod hfg, dom_le_dom hfg, ?_⟩
  intro x
  apply g.toEquiv.injective
  change g.toEquiv (inclusion _ (f.toEquiv.symm x)) = g.toEquiv (g.toEquiv.symm _)
  rw [g.toEquiv.apply_symm_apply, (Equiv.apply_symm_apply f.toEquiv x).symm,
    f.toEquiv.symm_apply_apply]
  exact toEquiv_inclusion_apply hfg _
/-
**FirstOrder.Language.PartialEquiv.monotone_symm** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.PartialEquiv`。
形式化陈述：monotone_symm : Monotone (fun (f : M ≃ₚ[L] N) => f.symm)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.symm_le_symm`：∀ {L : FirstOrder.Languag
e} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   
{f g : L.PartialEquiv M N}, f ≤ g →…
-/
theorem monotone_symm : Monotone (fun (f : M ≃ₚ[L] N) ↦ f.symm) := fun _ _ => symm_le_symm
/-
**FirstOrder.Language.PartialEquiv.symm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.PartialEquiv`。
形式化陈述：symm_le_iff {f : M ≃ₚ[L] N} {g : N ≃ₚ[L] M} : f.symm <= g ↔ f <= g.symm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.PartialEquiv.symm_symm`：symm_symm (f : M ≃ₚ[L] N) : 
f.symm.symm = f
· 使用定理 `FirstOrder.Language.PartialEquiv.monotone_symm`：monotone_symm : Monotone
 (fun (f : M ≃ₚ[L] N) => f.symm)
-/
theorem symm_le_iff {f : M ≃ₚ[L] N} {g : N ≃ₚ[L] M} : f.symm ≤ g ↔ f ≤ g.symm :=
  ⟨by intro h; rw [← f.symm_symm]; exact monotone_symm h,
    by intro h; rw  [← g.symm_symm]; exact monotone_symm h⟩
/-
**FirstOrder.Language.PartialEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.PartialEquiv`。
形式化陈述：ext {f g : M ≃ₚ[L] N} (h_dom : f.dom = g.dom) : (forall x : M, forall h : 
x in f.dom, subtype _ (f.toEquiv ⟨x, h⟩) = subtype _ (g.toEquiv ⟨x, (h_dom ▸ h)⟩
)) -> f = g
参数：h_dom : f.dom = g.dom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.ModelTheory.PartialEquiv.0.FirstOrder.Language.PartialE
quiv.le_antisymm`：∀ {L : FirstOrder.Language} {M : Type w} {N : Type w'} [inst :
 L.Structure M] [inst_1 : L.Structure N]   (f g : L.PartialEquiv M N), f ≤ g →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.PartialEquiv.le_def`：le_def (f g : M ≃ₚ[L] N) : f <=
 g ↔ exists h : f.dom <= g.dom, (subtype _).comp (g.toEquiv.toEmbedding.comp (Su
bstructure.inclusion h)) = (s…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem ext {f g : M ≃ₚ[L] N} (h_dom : f.dom = g.dom) : (∀ x : M, ∀ h : x ∈ f.dom,
    subtype _ (f.toEquiv ⟨x, h⟩) = subtype _ (g.toEquiv ⟨x, (h_dom ▸ h)⟩)) → f = g := by
  intro h
  rcases f with ⟨dom_f, cod_f, equiv_f⟩
  cases h_dom
  apply le_antisymm <;> (rw [le_def]; use le_rfl; ext ⟨x, hx⟩)
  · exact (h x hx).symm
  · exact h x hx
/-
**FirstOrder.Language.PartialEquiv.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.PartialEquiv`。
形式化陈述：ext_iff {f g : M ≃ₚ[L] N} : f = g ↔ exists h_dom : f.dom = g.dom, forall x
 : M, forall h : x in f.dom, subtype _ (f.toEquiv ⟨x, h⟩) = subtype _ (g.toEquiv
 ⟨x, (h_dom ▸ h)⟩)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.PartialEquiv.ext`：ext {f g : M ≃ₚ[L] N} (h_dom : f.d
om = g.dom) : (forall x : M, forall h : x in f.dom, subtype _ (f.toEquiv ⟨x, h⟩)
 = subtype _ (g.toEquiv ⟨x…
-/
theorem ext_iff {f g : M ≃ₚ[L] N} : f = g ↔ ∃ h_dom : f.dom = g.dom,
    ∀ x : M, ∀ h : x ∈ f.dom,
    subtype _ (f.toEquiv ⟨x, h⟩) = subtype _ (g.toEquiv ⟨x, (h_dom ▸ h)⟩) := by
  constructor
  · intro h_eq
    rcases f with ⟨dom_f, cod_f, equiv_f⟩
    cases h_eq
    exact ⟨rfl, fun _ _ ↦ rfl⟩
  · rintro ⟨h, H⟩; exact ext h H
/-
**FirstOrder.Language.PartialEquiv.monotone_dom** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.PartialEquiv`。
形式化陈述：monotone_dom : Monotone (fun f : M ≃ₚ[L] N => f.dom)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
-/
theorem monotone_dom : Monotone (fun f : M ≃ₚ[L] N ↦ f.dom) := fun _ _ ↦ dom_le_dom
/-
**FirstOrder.Language.PartialEquiv.monotone_cod** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.PartialEquiv`。
形式化陈述：monotone_cod : Monotone (fun f : M ≃ₚ[L] N => f.cod)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.cod_le_cod`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
-/
theorem monotone_cod : Monotone (fun f : M ≃ₚ[L] N ↦ f.cod) := fun _ _ ↦ cod_le_cod

/-- Restriction of a partial equivalence to a substructure of the domain. -/
/-
**FirstOrder.Language.PartialEquiv.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.PartialEquiv`。
形式化陈述：domRestrict (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A <= f.dom) : M ≃ₚ
[L] N
参数：f : M ≃ₚ[L] N；h : A <= f.dom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a partial equivalence to a substructure of the domain.
-/
noncomputable def domRestrict (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A ≤ f.dom) :
    M ≃ₚ[L] N := by
  let g := (subtype _).comp (f.toEquiv.toEmbedding.comp (A.inclusion h))
  exact {
    dom := A
    cod := g.toHom.range
    toEquiv := g.equivRange
  }
/-
**FirstOrder.Language.PartialEquiv.domRestrict_le** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.PartialEquiv`。
形式化陈述：domRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A <= f.dom) : f
.domRestrict h <= f
参数：f : M ≃ₚ[L] N；h : A <= f.dom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A ≤ f.dom) :
    f.domRestrict h ≤ f := ⟨h, rfl⟩
/-
**FirstOrder.Language.PartialEquiv.le_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.PartialEquiv`。
形式化陈述：le_domRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure M} (hf : f.dom <= A) 
(hg : A <= g.dom) (hfg : f <= g) : f <= g.domRestrict hg
参数：f g : M ≃ₚ[L] N；hf : f.dom <= A；hg : A <= g.dom；hfg : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.PartialEquiv.subtype_toEquiv_inclusion`：subtype_toEq
uiv_inclusion {f g : M ≃ₚ[L] N} (h : f <= g) : (subtype _).comp (g.toEquiv.toEmb
edding.comp (Substructure.inclusion (dom_le_dom …
-/
theorem le_domRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure M} (hf : f.dom ≤ A)
    (hg : A ≤ g.dom) (hfg : f ≤ g) : f ≤ g.domRestrict hg :=
  ⟨hf, by rw [← (subtype_toEquiv_inclusion hfg)]; rfl⟩

/-- Restriction of a partial equivalence to a substructure of the codomain. -/
/-
**FirstOrder.Language.PartialEquiv.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.PartialEquiv`。
形式化陈述：codRestrict (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A <= f.cod) : M ≃ₚ
[L] N
参数：f : M ≃ₚ[L] N；h : A <= f.cod。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a partial equivalence to a substructure of the codomain.
-/
noncomputable def codRestrict (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A ≤ f.cod) :
    M ≃ₚ[L] N :=
  (f.symm.domRestrict h).symm
/-
**FirstOrder.Language.PartialEquiv.codRestrict_le** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.PartialEquiv`。
形式化陈述：codRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A <= f.cod) : c
odRestrict f h <= f
参数：f : M ≃ₚ[L] N；h : A <= f.cod。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.PartialEquiv.symm_le_iff`：symm_le_iff {f : M ≃ₚ[L] N
} {g : N ≃ₚ[L] M} : f.symm <= g ↔ f <= g.symm
· 使用定理 `FirstOrder.Language.PartialEquiv.domRestrict_le`：domRestrict_le (f : M ≃
ₚ[L] N) {A : L.Substructure M} (h : A <= f.dom) : f.domRestrict h <= f
-/
theorem codRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A ≤ f.cod) :
    codRestrict f h ≤ f :=
  symm_le_iff.2 (f.symm.domRestrict_le h)
/-
**FirstOrder.Language.PartialEquiv.le_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.PartialEquiv`。
形式化陈述：le_codRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure N} (hf : f.cod <= A) 
(hg : A <= g.cod) (hfg : f <= g) : f <= g.codRestrict hg
参数：f g : M ≃ₚ[L] N；hf : f.cod <= A；hg : A <= g.cod；hfg : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.PartialEquiv.symm_le_iff`：symm_le_iff {f : M ≃ₚ[L] N
} {g : N ≃ₚ[L] M} : f.symm <= g ↔ f <= g.symm
· 使用定理 `FirstOrder.Language.PartialEquiv.le_domRestrict`：le_domRestrict (f g : M
 ≃ₚ[L] N) {A : L.Substructure M} (hf : f.dom <= A) (hg : A <= g.dom) (hfg : f <=
 g) : f <= g.domRestrict hg
· 使用定理 `FirstOrder.Language.PartialEquiv.monotone_symm`：monotone_symm : Monotone
 (fun (f : M ≃ₚ[L] N) => f.symm)
-/
theorem le_codRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure N} (hf : f.cod ≤ A)
    (hg : A ≤ g.cod) (hfg : f ≤ g) : f ≤ g.codRestrict hg :=
  symm_le_iff.1 (le_domRestrict f.symm g.symm hf hg (monotone_symm hfg))

/-- A partial equivalence as an embedding from its domain. -/
/-
**FirstOrder.Language.PartialEquiv.toEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.PartialEquiv`。
形式化陈述：toEmbedding (f : M ≃ₚ[L] N) : f.dom ↪[L] N
参数：f : M ≃ₚ[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial equivalence as an embedding from its domain.
-/
def toEmbedding (f : M ≃ₚ[L] N) : f.dom ↪[L] N :=
  (subtype _).comp f.toEquiv.toEmbedding

@[simp]
/-
**FirstOrder.Language.PartialEquiv.toEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.PartialEquiv`。
形式化陈述：toEmbedding_apply {f : M ≃ₚ[L] N} (m : f.dom) : f.toEmbedding m = f.toEqui
v m
参数：m : f.dom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEmbedding_apply {f : M ≃ₚ[L] N} (m : f.dom) :
    f.toEmbedding m = f.toEquiv m :=
  rfl

/-- Given a partial equivalence which has the whole structure as domain,
  returns the corresponding embedding. -/
/-
**FirstOrder.Language.PartialEquiv.toEmbeddingOfEqTop** 是 Mathlib 中的一个定义，位于命名空间 
`FirstOrder.Language.PartialEquiv`。
形式化陈述：toEmbeddingOfEqTop {f : M ≃ₚ[L] N} (h : f.dom = ⊤) : M ↪[L] N
参数：h : f.dom = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a partial equivalence which has the whole structure as domain,
  returns the corresponding embedding.
-/
def toEmbeddingOfEqTop {f : M ≃ₚ[L] N} (h : f.dom = ⊤) : M ↪[L] N :=
  (h ▸ f.toEmbedding).comp topEquiv.symm.toEmbedding

@[simp]
/-
**FirstOrder.Language.PartialEquiv.toEmbeddingOfEqTop_apply** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.PartialEquiv`。
形式化陈述：toEmbeddingOfEqTop_apply {f : M ≃ₚ[L] N} (h : f.dom = ⊤) (m : M) : toEmbed
dingOfEqTop h m = f.toEquiv ⟨m, h.symm ▸ mem_top m⟩
参数：h : f.dom = ⊤；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.mem_top`：mem_top (x : M) : x in (⊤ : L.
Substructure M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem toEmbeddingOfEqTop_apply {f : M ≃ₚ[L] N} (h : f.dom = ⊤) (m : M) :
    toEmbeddingOfEqTop h m = f.toEquiv ⟨m, h.symm ▸ mem_top m⟩ := by
  rcases f with ⟨dom, cod, g⟩
  cases h
  rfl

set_option linter.style.nameCheck false in
/-- Given a partial equivalence which has the whole structure as domain and
  as codomain, returns the corresponding equivalence. -/
/-
**FirstOrder.Language.PartialEquiv.toEquivOfEqTop** 是 Mathlib 中的一个定义，位于命名空间 `Fir
stOrder.Language.PartialEquiv`。
形式化陈述：toEquivOfEqTop {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤) (h_cod : f.cod = ⊤) : M
 ≃[L] N
参数：h_dom : f.dom = ⊤；h_cod : f.cod = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a partial equivalence which has the whole structure as domain and
  as codomain, returns the corresponding equivalence.
-/
def toEquivOfEqTop {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
    (h_cod : f.cod = ⊤) : M ≃[L] N :=
  (topEquiv (M := N)).comp ((h_dom ▸ h_cod ▸ f.toEquiv).comp (topEquiv (M := M)).symm)

@[simp]
/-
**FirstOrder.Language.PartialEquiv.toEquivOfEqTop_toEmbedding** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.PartialEquiv`。
形式化陈述：toEquivOfEqTop_toEmbedding {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤) (h_cod : f.
cod = ⊤) : (toEquivOfEqTop h_dom h_cod).toEmbedding = toEmbeddingOfEqTop h_dom
参数：h_dom : f.dom = ⊤；h_cod : f.cod = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem toEquivOfEqTop_toEmbedding {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
    (h_cod : f.cod = ⊤) :
    (toEquivOfEqTop h_dom h_cod).toEmbedding = toEmbeddingOfEqTop h_dom := by
  rcases f with ⟨dom, cod, g⟩
  cases h_dom
  cases h_cod
  rfl
/-
**FirstOrder.Language.PartialEquiv.dom_fg_iff_cod_fg** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.PartialEquiv`。
形式化陈述：dom_fg_iff_cod_fg {N : Type*} [L.Structure N] (f : M ≃ₚ[L] N) : f.dom.FG ↔
 f.cod.FG
参数：f : M ≃ₚ[L] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `FirstOrder.Language.Equiv.fg_iff`：∀ {L : FirstOrder.Language} {M : Type 
u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N]   (f : L.Equ
iv M N), FirstOrder.La…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dom_fg_iff_cod_fg {N : Type*} [L.Structure N] (f : M ≃ₚ[L] N) :
    f.dom.FG ↔ f.cod.FG := by
  rw [Substructure.fg_iff_structure_fg, f.toEquiv.fg_iff, Substructure.fg_iff_structure_fg]

end PartialEquiv

namespace Embedding

/-- Given an embedding, returns the corresponding partial equivalence with `⊤` as domain. -/
/-
**FirstOrder.Language.Embedding.toPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.Embedding`。
形式化陈述：toPartialEquiv (f : M ↪[L] N) : M ≃ₚ[L] N
参数：f : M ↪[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding, returns the corresponding partial equivalence with `⊤` as do
main.
-/
noncomputable def toPartialEquiv (f : M ↪[L] N) : M ≃ₚ[L] N :=
  ⟨⊤, f.toHom.range, f.equivRange.comp (Substructure.topEquiv)⟩
/-
**FirstOrder.Language.Embedding.toPartialEquiv_injective** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.Embedding`。
形式化陈述：toPartialEquiv_injective : Function.Injective (fun f : M ↪[L] N => f.toPar
tialEquiv)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.PartialEquiv.ext_iff`：ext_iff {f g : M ≃ₚ[L] N} : f 
= g ↔ exists h_dom : f.dom = g.dom, forall x : M, forall h : x in f.dom, subtype
 _ (f.toEquiv ⟨x, h⟩) = subtyp…
· 使用定理 `FirstOrder.Language.Substructure.mem_top`：mem_top (x : M) : x in (⊤ : L.
Substructure M)
-/
theorem toPartialEquiv_injective :
    Function.Injective (fun f : M ↪[L] N ↦ f.toPartialEquiv) := by
  intro _ _ h
  ext
  rw [PartialEquiv.ext_iff] at h
  rcases h with ⟨_, H⟩
  exact H _ (Substructure.mem_top _)

@[simp]
/-
**FirstOrder.Language.Embedding.toEmbedding_toPartialEquiv** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.Embedding`。
形式化陈述：toEmbedding_toPartialEquiv (f : M ↪[L] N) : PartialEquiv.toEmbeddingOfEqTo
p (f
参数：f : M ↪[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEmbedding_toPartialEquiv (f : M ↪[L] N) :
    PartialEquiv.toEmbeddingOfEqTop (f := f.toPartialEquiv) rfl = f :=
  rfl

@[simp]
/-
**FirstOrder.Language.Embedding.toPartialEquiv_toEmbedding** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.Embedding`。
形式化陈述：toPartialEquiv_toEmbedding {f : M ≃ₚ[L] N} (h : f.dom = ⊤) : (PartialEquiv
.toEmbeddingOfEqTop h).toPartialEquiv = f
参数：h : f.dom = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.ext`：ext {f g : M ≃ₚ[L] N} (h_dom : f.d
om = g.dom) : (forall x : M, forall h : x in f.dom, subtype _ (f.toEquiv ⟨x, h⟩)
 = subtype _ (g.toEquiv ⟨x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem toPartialEquiv_toEmbedding {f : M ≃ₚ[L] N} (h : f.dom = ⊤) :
    (PartialEquiv.toEmbeddingOfEqTop h).toPartialEquiv = f := by
  rcases f with ⟨_, _, _⟩
  cases h
  apply PartialEquiv.ext
  · intro _ _
    rfl
  · rfl

end Embedding

namespace DirectLimit

open PartialEquiv

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (S : ι →o M ≃ₚ[L] N)

/-
**FirstOrder.Language.DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Languag
e.DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DirectedSystem (fun i ↦ (S i).dom)
    (fun _ _ h ↦ Substructure.inclusion (dom_le_dom (S.monotone h))) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl
/-
**FirstOrder.Language.DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Languag
e.DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DirectedSystem (fun i ↦ (S i).cod)
    (fun _ _ h ↦ Substructure.inclusion (cod_le_cod (S.monotone h))) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The limit of a directed system of PartialEquivs. -/
/-
**FirstOrder.Language.DirectLimit.partialEquivLimit** 是 Mathlib 中的一个定义，位于命名空间 `F
irstOrder.Language.DirectLimit`。
形式化陈述：partialEquivLimit : M ≃ₚ[L] N where dom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.DirectLimit.instDirectedSystemSubtypeMemSubstructure
DomCoeOrderHomPartialEquivEmbeddingInclusion`：∀ {L : FirstOrder.Language} {M : T
ype w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {ι : Type u
_1}   [inst_2 : Preorder ι…
· 使用定理 `FirstOrder.Language.DirectLimit.instDirectedSystemSubtypeMemSubstructure
CodCoeOrderHomPartialEquivEmbeddingInclusion`：∀ {L : FirstOrder.Language} {M : T
ype w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {ι : Type u
_1}   [inst_2 : Preorder ι…

--- 原说明 ---
The limit of a directed system of PartialEquivs.
-/
noncomputable def partialEquivLimit : M ≃ₚ[L] N where
  dom := iSup (fun i ↦ (S i).dom)
  cod := iSup (fun i ↦ (S i).cod)
  toEquiv :=
    (Equiv_iSup {
      toFun := (fun i ↦ (S i).cod)
      monotone' := monotone_cod.comp S.monotone }).comp
      ((DirectLimit.equiv_lift L ι (fun i ↦ (S i).dom)
        (fun _ _ hij ↦ Substructure.inclusion (dom_le_dom (S.monotone hij)))
        (fun i ↦ (S i).cod)
        (fun _ _ hij ↦ Substructure.inclusion (cod_le_cod (S.monotone hij)))
        (fun i ↦ (S i).toEquiv)
        (fun _ _ hij _ ↦ toEquiv_inclusion_apply (S.monotone hij) _)).comp
        (Equiv_iSup {
          toFun := (fun i ↦ (S i).dom)
          monotone' := monotone_dom.comp S.monotone }).symm)

@[simp]
/-
**FirstOrder.Language.DirectLimit.dom_partialEquivLimit** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.DirectLimit`。
形式化陈述：dom_partialEquivLimit : (partialEquivLimit S).dom = iSup (fun x => (S x).d
om)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dom_partialEquivLimit : (partialEquivLimit S).dom = iSup (fun x ↦ (S x).dom) := rfl

@[simp]
/-
**FirstOrder.Language.DirectLimit.cod_partialEquivLimit** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.DirectLimit`。
形式化陈述：cod_partialEquivLimit : (partialEquivLimit S).cod = iSup (fun x => (S x).c
od)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cod_partialEquivLimit : (partialEquivLimit S).cod = iSup (fun x ↦ (S x).cod) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FirstOrder.Language.DirectLimit.partialEquivLimit_comp_inclusion** 是 Mathlib 中
的一个引理，位于命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：partialEquivLimit_comp_inclusion {i : ι} : (partialEquivLimit S).toEquiv.t
oEmbedding.comp (Substructure.inclusion (le_iSup _ i)) = (Substructure.inclusion
 (le_iSup _ i)).comp (S i).toEquiv.toEmbedding
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `FirstOrder.Language.DirectLimit.instDirectedSystemSubtypeMemSubstructure
DomCoeOrderHomPartialEquivEmbeddingInclusion`：∀ {L : FirstOrder.Language} {M : T
ype w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {ι : Type u
_1}   [inst_2 : Preorder ι…
· 使用定理 `FirstOrder.Language.DirectLimit.instDirectedSystemSubtypeMemSubstructure
CodCoeOrderHomPartialEquivEmbeddingInclusion`：∀ {L : FirstOrder.Language} {M : T
ype w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {ι : Type u
_1}   [inst_2 : Preorder ι…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `FirstOrder.Language.instDirectedSystemSubtypeMemSubstructureCoeOrderHomE
mbeddingInclusion`：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] 
{M : Type u_1} [inst_1 : L.Structure M]   (S : ι →o L.Substructure M),   Direct…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.DirectLimit.Equiv_isup_symm_inclusion`：Equiv_isup_sy
mm_inclusion (i : ι) : (Equiv_iSup S).symm.toEmbedding.comp (Substructure.inclus
ion (le_iSup _ _)) = of L ι _ (fun _ _ h => Sub…
-/
lemma partialEquivLimit_comp_inclusion {i : ι} :
    (partialEquivLimit S).toEquiv.toEmbedding.comp (Substructure.inclusion (le_iSup _ i)) =
    (Substructure.inclusion (le_iSup _ i)).comp (S i).toEquiv.toEmbedding := by
  simp only [partialEquivLimit, Equiv.comp_toEmbedding, Embedding.comp_assoc]
  rw [Equiv_isup_symm_inclusion]
  congr

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.DirectLimit.le_partialEquivLimit** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.DirectLimit`。
形式化陈述：le_partialEquivLimit (i : ι) : S i <= partialEquivLimit S
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FirstOrder.Language.DirectLimit.partialEquivLimit_comp_inclusion`：partia
lEquivLimit_comp_inclusion {i : ι} : (partialEquivLimit S).toEquiv.toEmbedding.c
omp (Substructure.inclusion (le_iSup _ i)) = (Substruc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_partialEquivLimit (i : ι) : S i ≤ partialEquivLimit S :=
  ⟨le_iSup (f := fun i ↦ (S i).dom) _, by
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
    these two `simp` calls cannot be combined. -/
    simp only [partialEquivLimit_comp_inclusion]
    simp only [cod_partialEquivLimit, ← Embedding.comp_assoc,
      subtype_comp_inclusion]⟩

end DirectLimit

section FGEquiv

open PartialEquiv Set Language.DirectLimit

variable (M) (N) (L)

/-- The type of equivalences between finitely generated substructures. -/
/-
**FirstOrder.Language.FGEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：FGEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of equivalences between finitely generated substructures.
-/
abbrev FGEquiv := {f : M ≃ₚ[L] N // f.dom.FG}

/-- Two structures `M` and `N` form an extension pair if the domain of any finitely-generated map
from `M` to `N` can be extended to include any element of `M`. -/
/-
**FirstOrder.Language.IsExtensionPair** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage`。
形式化陈述：IsExtensionPair : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two structures `M` and `N` form an extension pair if the domain of any finitely-
generated map
from `M` to `N` can be extended to include any element of `M`.
-/
def IsExtensionPair : Prop := ∀ (f : L.FGEquiv M N) (m : M), ∃ g, m ∈ g.1.dom ∧ f ≤ g

variable {M N L}
/-
**FirstOrder.Language.countable_self_fgequiv_of_countable** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language`。
形式化陈述：countable_self_fgequiv_of_countable [Countable M] : Countable (L.FGEquiv M
 M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `FirstOrder.Language.PartialEquiv.ext`：ext {f g : M ≃ₚ[L] N} (h_dom : f.d
om = g.dom) : (forall x : M, forall h : x in f.dom, subtype _ (f.toEquiv ⟨x, h⟩)
 = subtype _ (g.toEquiv ⟨x…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `Function.Embedding.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
(f : α ↪ β), Countable α
· 使用定理 `instCountableSigma`：∀ {α : Type u} {π : α → Type w} [Countable α] [∀ (a 
: α), Countable (π a)], Countable (Sigma π)
· 使用定理 `FirstOrder.Language.Substructure.instCountable_fg_substructures_of_count
able`：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] [Countab
le M], Countable { S // S.FG }
· 使用定理 `FirstOrder.Language.Structure.FG.instCountable_hom`：∀ {L : FirstOrder.La
nguage} {M : Type u_1} [inst : L.Structure M] (N : Type u_2) [inst_1 : L.Structu
re N] [Countable N]   [h : FirstOrder.La…
-/
theorem countable_self_fgequiv_of_countable [Countable M] :
    Countable (L.FGEquiv M M) := by
  let g : L.FGEquiv M M →
      Σ U : { S : L.Substructure M // S.FG }, U.val →[L] M :=
    fun f ↦ ⟨⟨f.val.dom, f.prop⟩, (subtype _).toHom.comp f.val.toEquiv.toHom⟩
  have g_inj : Function.Injective g := by
    intro f f' h
    ext
    let ⟨⟨dom_f, cod_f, equiv_f⟩, f_fin⟩ := f
    cases congr_arg (·.1) h
    apply PartialEquiv.ext (by rfl)
    simp only [g, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact fun x hx ↦ congr_fun (congr_arg (↑) h) ⟨x, hx⟩
  have : ∀ U : { S : L.Substructure M // S.FG }, Structure.FG L U.val :=
    fun U ↦ (U.val.fg_iff_structure_fg.1 U.prop)
  exact Function.Embedding.countable ⟨g, g_inj⟩
/-
**FirstOrder.Language.inhabited_self_FGEquiv** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：inhabited_self_FGEquiv : Inhabited (L.FGEquiv M M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.fg_bot`：fg_bot : (⊥ : L.Substructure M)
.FG
-/
instance inhabited_self_FGEquiv : Inhabited (L.FGEquiv M M) :=
  ⟨⟨⟨⊥, ⊥, Equiv.refl L (⊥ : L.Substructure M)⟩, fg_bot⟩⟩
/-
**FirstOrder.Language.inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations** 是 M
athlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
形式化陈述：inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations [IsEmpty L.Constants]
 [IsEmpty (L.Relations 0)] : Inhabited (L.FGEquiv M N)
参数：L.Relations 0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.instIsEmptySubtypeMemBotOfConstants`：∀ 
(L : FirstOrder.Language) (M : Type w) [inst : L.Structure M] [IsEmpty L.Constan
ts], IsEmpty ↥⊥
· 使用定理 `FirstOrder.Language.Substructure.fg_bot`：fg_bot : (⊥ : L.Substructure M)
.FG
-/
instance inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations
    [IsEmpty L.Constants] [IsEmpty (L.Relations 0)] : Inhabited (L.FGEquiv M N) :=
  ⟨⟨⟨⊥, ⊥, {
      toFun := isEmptyElim
      invFun := isEmptyElim
      left_inv := isEmptyElim
      right_inv := isEmptyElim
      map_fun' := fun {n} f x => by
        subsingleton
      map_rel' := fun {n} r x => by
        cases n
        · exact isEmptyElim r
        · exact isEmptyElim (x 0)
    }⟩, fg_bot⟩⟩

/-- Maps to the symmetric finitely-generated partial equivalence. -/
@[simps]
/-
**FirstOrder.Language.FGEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.FGEquiv`。
形式化陈述：{L : FirstOrder.Language} →   {M : Type w} → {N : Type w'} → [inst : L.Str
ucture M] → [inst_1 : L.Structure N] → L.FGEquiv M N → L.FGEquiv N M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps to the symmetric finitely-generated partial equivalence.
-/
def FGEquiv.symm (f : L.FGEquiv M N) : L.FGEquiv N M := ⟨f.1.symm, f.1.dom_fg_iff_cod_fg.1 f.2⟩
/-
**FirstOrder.Language.isExtensionPair_iff_cod** 是 Mathlib 中的一个引理，位于命名空间 `FirstOr
der.Language`。
形式化陈述：isExtensionPair_iff_cod : L.IsExtensionPair M N ↔ forall (f : L.FGEquiv N 
M) (m : M), exists g, m in g.1.cod ∧ f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.PartialEquiv.monotone_symm`：monotone_symm : Monotone
 (fun (f : M ≃ₚ[L] N) => f.symm)
-/
lemma isExtensionPair_iff_cod : L.IsExtensionPair M N ↔
    ∀ (f : L.FGEquiv N M) (m : M), ∃ g, m ∈ g.1.cod ∧ f ≤ g := by
  refine Iff.intro ?_ ?_ <;>
  · intro h f m
    obtain ⟨g, h1, h2⟩ := h f.symm m
    exact ⟨g.symm, h1, monotone_symm h2⟩

/-- An alternate characterization of an extension pair is that every finitely generated partial
isomorphism can be extended to include any particular element of the domain. -/
/-
**FirstOrder.Language.isExtensionPair_iff_exists_embedding_closure_singleton_sup
** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language`。
形式化陈述：isExtensionPair_iff_exists_embedding_closure_singleton_sup : L.IsExtension
Pair M N ↔ forall (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] N) (m : M), exis
ts g : (closure L {m} ⊔ S : L.Substructure M) ↪[L] N, f = g.comp (Substructure.i
nclusion le_sup_right)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Embedding.subtype_equivRange`：subtype_equivRange (f 
: M ↪[L] N) : (subtype _).comp f.equivRange.toEmbedding = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FirstOrder.Language.Substructure.FG.sup`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N₁ N₂ : L.Substructure M},   N₁.FG → N₂.FG →
 (N₁ ⊔ N₂).FG
· 使用定理 `FirstOrder.Language.Substructure.fg_closure_singleton`：fg_closure_single
ton (x : M) : FG (closure L ({x} : Set M))
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `FirstOrder.Language.PartialEquiv.toEmbedding.eq_1`：∀ {L : FirstOrder.Lan
guage} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N
]   (f : L.PartialEquiv M N), f.toEmbed…

--- 原说明 ---
An alternate characterization of an extension pair is that every finitely genera
ted partial
isomorphism can be extended to include any particular element of the domain.
-/
theorem isExtensionPair_iff_exists_embedding_closure_singleton_sup :
    L.IsExtensionPair M N ↔
    ∀ (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] N) (m : M),
      ∃ g : (closure L {m} ⊔ S : L.Substructure M) ↪[L] N, f =
        g.comp (Substructure.inclusion le_sup_right) := by
  refine ⟨fun h S S_FG f m => ?_, fun h ⟨f, f_FG⟩ m => ?_⟩
  · obtain ⟨⟨f', hf'⟩, mf', ff'1, ff'2⟩ := h ⟨⟨S, _, f.equivRange⟩, S_FG⟩ m
    refine ⟨f'.toEmbedding.comp (Substructure.inclusion ?_), ?_⟩
    · simp only [sup_le_iff, ff'1, closure_le, singleton_subset_iff, SetLike.mem_coe, mf',
        and_self]
    · ext ⟨x, hx⟩
      rw [Embedding.subtype_equivRange] at ff'2
      simp only [← ff'2, Embedding.comp_apply, Substructure.coe_inclusion,
        Equiv.coe_toEmbedding, coe_subtype, PartialEquiv.toEmbedding_apply]
  · obtain ⟨f', eq_f'⟩ := h f.dom f_FG f.toEmbedding m
    refine ⟨⟨⟨closure L {m} ⊔ f.dom, f'.toHom.range, f'.equivRange⟩,
      (fg_closure_singleton _).sup f_FG⟩,
      subset_closure.trans (le_sup_left : (closure L) {m} ≤ _) (mem_singleton m),
      ⟨le_sup_right, Embedding.ext (fun _ => ?_)⟩⟩
    rw [PartialEquiv.toEmbedding] at eq_f'
    simp only [Embedding.comp_apply, Substructure.coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
      Embedding.equivRange_apply, eq_f']

namespace IsExtensionPair

protected alias ⟨cod, _⟩ := isExtensionPair_iff_cod

/-- The cofinal set of finite equivalences with a given element in their domain. -/
/-
**FirstOrder.Language.IsExtensionPair.definedAtLeft** 是 Mathlib 中的一个定义，位于命名空间 `F
irstOrder.Language.IsExtensionPair`。
形式化陈述：definedAtLeft (h : L.IsExtensionPair M N) (m : M) : Order.Cofinal (FGEquiv
 L M N) where carrier
参数：h : L.IsExtensionPair M N；m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofinal set of finite equivalences with a given element in their domain.
-/
def definedAtLeft
    (h : L.IsExtensionPair M N) (m : M) : Order.Cofinal (FGEquiv L M N) where
  carrier := {f | m ∈ f.val.dom}
  isCofinal := fun f => h f m

/-- The cofinal set of finite equivalences with a given element in their codomain. -/
/-
**FirstOrder.Language.IsExtensionPair.definedAtRight** 是 Mathlib 中的一个定义，位于命名空间 `
FirstOrder.Language.IsExtensionPair`。
形式化陈述：definedAtRight (h : L.IsExtensionPair N M) (n : N) : Order.Cofinal (FGEqui
v L M N) where carrier
参数：h : L.IsExtensionPair N M；n : N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.IsExtensionPair.cod`：∀ {L : FirstOrder.Language} {M 
: Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   L.IsE
xtensionPair M N → ∀ (f : L.F…

--- 原说明 ---
The cofinal set of finite equivalences with a given element in their codomain.
-/
def definedAtRight
    (h : L.IsExtensionPair N M) (n : N) : Order.Cofinal (FGEquiv L M N) where
  carrier := {f | n ∈ f.val.cod}
  isCofinal := fun f => h.cod f n

end IsExtensionPair

/-- For a countably generated structure `M` and a structure `N`, if any partial equivalence
between finitely generated substructures can be extended to any element in the domain,
then there exists an embedding of `M` in `N`. -/
/-
**FirstOrder.Language.embedding_from_cg** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage`。
形式化陈述：embedding_from_cg (M_cg : Structure.CG L M) (g : L.FGEquiv M N) (H : L.IsE
xtensionPair M N) : exists f : M ↪[L] N, g <= f.toPartialEquiv
参数：M_cg : Structure.CG L M；g : L.FGEquiv M N；H : L.IsExtensionPair M N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Order.sequenceOfCofinals.monotone`：∀ {P : Type u_1} [inst : Preorder P] 
(p : P) {ι : Type u_2} [inst_1 : Encodable ι] (𝒟 : ι → Order.Cofinal P),   Monot
one (Order.sequenceOfCo…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Order.sequenceOfCofinals.encode_mem`：∀ {P : Type u_1} [inst : Preorder P
] (p : P) {ι : Type u_2} [inst_1 : Encodable ι] (𝒟 : ι → Order.Cofinal P) (i : ι
),   Order.sequenceOfCofi…
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `FirstOrder.Language.DirectLimit.le_partialEquivLimit`：le_partialEquivLim
it (i : ι) : S i <= partialEquivLimit S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `FirstOrder.Language.Substructure.closure_le`：closure_le : closure L s <=
 S ↔ s subseteq S
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `FirstOrder.Language.Embedding.toPartialEquiv_toEmbedding`：toPartialEquiv
_toEmbedding {f : M ≃ₚ[L] N} (h : f.dom = ⊤) : (PartialEquiv.toEmbeddingOfEqTop 
h).toPartialEquiv = f

--- 原说明 ---
For a countably generated structure `M` and a structure `N`, if any partial equi
valence
between finitely generated substructures can be extended to any element in the d
omain,
then there exists an embedding of `M` in `N`.
-/
theorem embedding_from_cg (M_cg : Structure.CG L M) (g : L.FGEquiv M N)
    (H : L.IsExtensionPair M N) :
    ∃ f : M ↪[L] N, g ≤ f.toPartialEquiv := by
  rcases M_cg with ⟨X, _, X_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  let D : X → Order.Cofinal (FGEquiv L M N) := fun x ↦ H.definedAtLeft x
  let S : ℕ →o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := DirectLimit.partialEquivLimit S
  have _ : X ⊆ F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D ⟨x, hx⟩
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (⟨x, hx⟩ : X) + 1)) this
  have isTop : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  exact ⟨toEmbeddingOfEqTop isTop,
        by convert! (le_partialEquivLimit S 0); apply Embedding.toPartialEquiv_toEmbedding⟩

/-- For two countably generated structure `M` and `N`, if any PartialEquiv
between finitely generated substructures can be extended to any element in the domain and to
any element in the codomain, then there exists an equivalence between `M` and `N`. -/
/-
**FirstOrder.Language.equiv_between_cg** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：equiv_between_cg (M_cg : Structure.CG L M) (N_cg : Structure.CG L N) (g : 
L.FGEquiv M N) (ext_dom : L.IsExtensionPair M N) (ext_cod : L.IsExtensionPair N 
M) : exists f : M ≃[L] N, g <= f.toEmbedding.toPartialEquiv
参数：M_cg : Structure.CG L M；N_cg : Structure.CG L N；g : L.FGEquiv M N；ext_dom : L
.IsExtensionPair M N；ext_cod : L.IsExtensionPair N M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Order.sequenceOfCofinals.monotone`：∀ {P : Type u_1} [inst : Preorder P] 
(p : P) {ι : Type u_2} [inst_1 : Encodable ι] (𝒟 : ι → Order.Cofinal P),   Monot
one (Order.sequenceOfCo…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Order.sequenceOfCofinals.encode_mem`：∀ {P : Type u_1} [inst : Preorder P
] (p : P) {ι : Type u_2} [inst_1 : Encodable ι] (𝒟 : ι → Order.Cofinal P) (i : ι
),   Order.sequenceOfCofi…
· 使用定理 `FirstOrder.Language.PartialEquiv.dom_le_dom`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `FirstOrder.Language.DirectLimit.le_partialEquivLimit`：le_partialEquivLim
it (i : ι) : S i <= partialEquivLimit S
· 使用定理 `FirstOrder.Language.PartialEquiv.cod_le_cod`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f
 g : L.PartialEquiv M N}, f ≤ g →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `FirstOrder.Language.Substructure.closure_le`：closure_le : closure L s <=
 S ↔ s subseteq S
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `FirstOrder.Language.PartialEquiv.toEquivOfEqTop_toEmbedding`：toEquivOfEq
Top_toEmbedding {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤) (h_cod : f.cod = ⊤) : (toEqu
ivOfEqTop h_dom h_cod).toEmbedding = toEmbeddingO…
· 使用定理 `FirstOrder.Language.Embedding.toPartialEquiv_toEmbedding`：toPartialEquiv
_toEmbedding {f : M ≃ₚ[L] N} (h : f.dom = ⊤) : (PartialEquiv.toEmbeddingOfEqTop 
h).toPartialEquiv = f

--- 原说明 ---
For two countably generated structure `M` and `N`, if any PartialEquiv
between finitely generated substructures can be extended to any element in the d
omain and to
any element in the codomain, then there exists an equivalence between `M` and `N
`.
-/
theorem equiv_between_cg (M_cg : Structure.CG L M) (N_cg : Structure.CG L N)
    (g : L.FGEquiv M N)
    (ext_dom : L.IsExtensionPair M N)
    (ext_cod : L.IsExtensionPair N M) :
    ∃ f : M ≃[L] N, g ≤ f.toEmbedding.toPartialEquiv := by
  rcases M_cg with ⟨X, X_count, X_gen⟩
  rcases N_cg with ⟨Y, Y_count, Y_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  have _ : Countable (↑Y : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑Y : Type _) := Encodable.ofCountable _
  let D : Sum X Y → Order.Cofinal (FGEquiv L M N) := fun p ↦
    Sum.recOn p (fun x ↦ ext_dom.definedAtLeft x) (fun y ↦ ext_cod.definedAtRight y)
  let S : ℕ →o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := @DirectLimit.partialEquivLimit L M N _ _ ℕ _ _ _ S
  have _ : X ⊆ F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inl ⟨x, hx⟩)
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (Sum.inl (⟨x, hx⟩ : X)) + 1)) this
  have _ : Y ⊆ F.cod := by
    intro y hy
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inr ⟨y, hy⟩)
    exact cod_le_cod
      (le_partialEquivLimit S (Encodable.encode (Sum.inr (⟨y, hy⟩ : Y)) + 1)) this
  have dom_top : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  have cod_top : F.cod = ⊤ := by rwa [← top_le_iff, ← Y_gen, Substructure.closure_le]
  refine ⟨toEquivOfEqTop dom_top cod_top, ?_⟩
  convert! le_partialEquivLimit S 0
  rw [toEquivOfEqTop_toEmbedding]
  apply Embedding.toPartialEquiv_toEmbedding

end FGEquiv

end Language

end FirstOrder

