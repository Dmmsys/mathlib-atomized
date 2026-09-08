/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Centroid
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.AffineSpace.Pointwise
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Affine bases and barycentric coordinates

Suppose `P` is an affine space modelled on the module `V` over the ring `k`, and `p : ι → P` is an
affine-independent family of points spanning `P`. Given this data, each point `q : P` may be written
uniquely as an affine combination: `q = w₀ p₀ + w₁ p₁ + ⋯` for some (finitely-supported) weights
`wᵢ`. For each `i : ι`, we thus have an affine map `P →ᵃ[k] k`, namely `q ↦ wᵢ`. This family of
maps is known as the family of barycentric coordinates. It is defined in this file.

## The construction

Fixing `i : ι`, and allowing `j : ι` to range over the values `j ≠ i`, we obtain a basis `bᵢ` of `V`
defined by `bᵢ j = p j -ᵥ p i`. Let `fᵢ j : V →ₗ[k] k` be the corresponding dual basis and let
`fᵢ = ∑ j, fᵢ j : V →ₗ[k] k` be the corresponding "sum of all coordinates" form. Then the `i`th
barycentric coordinate of `q : P` is `1 - fᵢ (q -ᵥ p i)`.

## Main definitions

* `fintypeAffineCoords`: the `AffineSubspace` of `ι → k` (for `Fintype ι`) where coordinates sum
  to `1`.
* `finsuppAffineCoords`: the `AffineSubspace` of `ι →₀ k` where coordinates sum to `1`.
* `AffineBasis`: a structure representing an affine basis of an affine space.
* `AffineBasis.coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
* `AffineBasis.coord_apply_eq`: the behaviour of `AffineBasis.coord i` on `p i`.
* `AffineBasis.coord_apply_ne`: the behaviour of `AffineBasis.coord i` on `p j` when `j ≠ i`.
* `AffineBasis.coord_apply`: the behaviour of `AffineBasis.coord i` on `p j` for general `j`.
* `AffineBasis.coord_apply_combination`: the characterisation of `AffineBasis.coord i` in terms
  of affine combinations, i.e., `AffineBasis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

* Construct the affine equivalence between `P` and `finsuppAffineCoords ι k`.

-/

@[expose] public section

open Affine Module Set
open scoped Pointwise

section Coordinates

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

variable (ι k) in
/-- The space of coordinates for affine combinations indexed by a `Fintype`. -/
/-
**fintypeAffineCoords** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypeAffineCoords [Fintype ι] : AffineSubspace k (ι -> k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of coordinates for affine combinations indexed by a `Fintype`.
-/
def fintypeAffineCoords [Fintype ι] : AffineSubspace k (ι → k) :=
  (affineSpan k {(1 : k)}).comap (Fintype.linearCombination k (1 : ι → k)).toAffineMap
/-
**mem_fintypeAffineCoords_iff_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_fintypeAffineCoords_iff_sum [Fintype ι] {w : ι -> k} : w in fintypeAff
ineCoords ι k ↔ ∑ i, w i = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_fintypeAffineCoords_iff_sum [Fintype ι] {w : ι → k} :
    w ∈ fintypeAffineCoords ι k ↔ ∑ i, w i = 1 := by
  simp [fintypeAffineCoords, Fintype.linearCombination_apply]
/-
**AffineIndependent.injOn_affineCombination_fintypeAffineCoords** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：AffineIndependent.injOn_affineCombination_fintypeAffineCoords [Fintype ι] 
{p : ι -> P} (h : AffineIndependent k p) : InjOn (Finset.univ.affineCombination 
k p) (fintypeAffineCoords ι k)
参数：h : AffineIndependent k p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff_eq_of_fintype_affineCombination_eq`：affineIndepend
ent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι -> P) : AffineInde
pendent k p ↔ forall w1 w2 : ι -> k, ∑ i, w1 i…
· 使用引理 `mem_fintypeAffineCoords_iff_sum`：mem_fintypeAffineCoords_iff_sum [Fintyp
e ι] {w : ι -> k} : w in fintypeAffineCoords ι k ↔ ∑ i, w i = 1
-/
lemma AffineIndependent.injOn_affineCombination_fintypeAffineCoords [Fintype ι] {p : ι → P}
    (h : AffineIndependent k p) :
    InjOn (Finset.univ.affineCombination k p) (fintypeAffineCoords ι k) :=
  fun w₁ hw₁ w₂ hw₂ he ↦ (affineIndependent_iff_eq_of_fintype_affineCombination_eq k p).1
    h w₁ w₂ (mem_fintypeAffineCoords_iff_sum.1 hw₁) (mem_fintypeAffineCoords_iff_sum.1 hw₂) he

variable (ι k) in
/-- The space of coordinates for affine combinations indexed by a general type. -/
/-
**finsuppAffineCoords** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppAffineCoords : AffineSubspace k (ι ->₀ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of coordinates for affine combinations indexed by a general type.
-/
noncomputable def finsuppAffineCoords : AffineSubspace k (ι →₀ k) :=
  (affineSpan k {(1 : k)}).comap (Finsupp.linearCombination k (1 : ι → k)).toAffineMap
/-
**mem_finsuppAffineCoords_iff_linearCombination** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_finsuppAffineCoords_iff_linearCombination {w : ι ->₀ k} : w in finsupp
AffineCoords ι k ↔ Finsupp.linearCombination k (1 : ι -> k) w = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_finsuppAffineCoords_iff_linearCombination {w : ι →₀ k} :
    w ∈ finsuppAffineCoords ι k ↔ Finsupp.linearCombination k (1 : ι → k) w = 1 := by
  simp [finsuppAffineCoords]

end Coordinates

universe u₁ u₂ u₃ u₄

/-- An affine basis is a family of affine-independent points whose span is the top subspace. -/
/-
**AffineBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u₁ →   (k : Type u₂) →     {V : Type u₃} →       (P : Type u₄) →     
    [inst : AddCommGroup V] → [AddTorsor V P] → [inst_2 : Ring k] → [_root_.Modu
le k V] → Type (max u₁ u₄)
参数：k : Type u₂；P : Type u₄；max u₁ u₄。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine basis is a family of affine-independent points whose span is the top s
ubspace.
-/
structure AffineBasis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroup V]
  [AffineSpace V P] [Ring k] [Module k V] where
  /-- The underlying family of points.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : ι → P
  protected ind' : AffineIndependent k toFun
  protected tot' : affineSpan k (range toFun) = ⊤

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AffineSpace V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

/-- The unique point in a single-point space is the simplest example of an affine basis. -/
/-
**AffineBasis.** 是 Mathlib 中的一个实例，位于命名空间 `AffineBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique point in a single-point space is the simplest example of an affine ba
sis.
-/
instance : Inhabited (AffineBasis PUnit k PUnit) :=
  ⟨⟨id, affineIndependent_of_subsingleton k id, by simp⟩⟩
/-
**AffineBasis.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `AffineBasis`。
形式化陈述：instFunLike : FunLike (AffineBasis ι k P) ι P where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (AffineBasis ι k P) ι P where
  coe := AffineBasis.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
/-
**AffineBasis.ext** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：ext {b₁ b₂ : AffineBasis ι k P} (h : (b₁ : ι -> P) = b₂) : b₁ = b₂
参数：h : (b₁ : ι -> P) = b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem ext {b₁ b₂ : AffineBasis ι k P} (h : (b₁ : ι → P) = b₂) : b₁ = b₂ :=
  DFunLike.coe_injective h
/-
**AffineBasis.ind** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：ind : AffineIndependent k b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.ind'`：∀ {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type 
u₄} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k] [inst_3
 : _ro…
-/
theorem ind : AffineIndependent k b :=
  b.ind'
/-
**AffineBasis.tot** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：tot : affineSpan k (range b) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.tot'`：∀ {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type 
u₄} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k] [inst_3
 : _ro…
-/
theorem tot : affineSpan k (range b) = ⊤ :=
  b.tot'

include b in
/-
**AffineBasis.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6} {P : Type u_7} [inst : AddC
ommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k] [inst_3 : _root_.Module
 k V] (b : AffineBasis ι k P), Nonempty ι
参数：b : AffineBasis ι k P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `AffineSubspace.instNontrivial`：∀ (k : Type u_1) (V : Type u_2) (P : Type
 u_3) [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
S : AddTorsor V P],…
· 使用定理 `AffineBasis.tot`：tot : affineSpan k (range b) = ⊤
-/
protected theorem nonempty : Nonempty ι :=
  not_isEmpty_iff.mp fun hι => by
    simpa only [@range_eq_empty _ _ hι, AffineSubspace.span_empty, bot_ne_top] using b.tot

/-- Composition of an affine basis and an equivalence of index types. -/
/-
**AffineBasis.reindex** 是 Mathlib 中的一个定义，位于命名空间 `AffineBasis`。
形式化陈述：reindex (e : ι ≃ ι') : AffineBasis ι' k P
参数：e : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Composition of an affine basis and an equivalence of index types.
-/
def reindex (e : ι ≃ ι') : AffineBasis ι' k P :=
  ⟨b ∘ e.symm, b.ind.comp_embedding e.symm.toEmbedding, by
    rw [e.symm.surjective.range_comp]
    exact b.3⟩

@[simp, norm_cast]
/-
**AffineBasis.coe_reindex** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：coe_reindex : ⇑(b.reindex e) = b ∘ e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_reindex : ⇑(b.reindex e) = b ∘ e.symm :=
  rfl

@[simp]
/-
**AffineBasis.reindex_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i')
参数：i' : ι'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  rfl

@[simp]
/-
**AffineBasis.reindex_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：reindex_refl : b.reindex (Equiv.refl _) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.ext`：ext {b₁ b₂ : AffineBasis ι k P} (h : (b₁ : ι -> P) = b₂
) : b₁ = b₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem reindex_refl : b.reindex (Equiv.refl _) = b :=
  ext rfl

/-- Given an affine basis for an affine space `P`, if we single out one member of the family, we
obtain a linear basis for the model space `V`.

The linear basis corresponding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}`
and its `j`th element is `b j -ᵥ b i`. (See `basisOf_apply`.) -/
/-
**AffineBasis.basisOf** 是 Mathlib 中的一个定义，位于命名空间 `AffineBasis`。
形式化陈述：basisOf (i : ι) : Basis { j : ι // j != i } k V
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an affine basis for an affine space `P`, if we single out one member of th
e family, we
obtain a linear basis for the model space `V`.

The linear basis corresponding to the singled-out member `i : ι` is indexed by `
{j : ι // j ≠ i}`
and its `j`th element is `b j -ᵥ b i`. (See `basisOf_apply`.)
-/
noncomputable def basisOf (i : ι) : Basis { j : ι // j ≠ i } k V :=
  Basis.mk ((affineIndependent_iff_linearIndependent_vsub k b i).mp b.ind)
    (by
      suffices
        Submodule.span k (range fun j : { x // x ≠ i } => b ↑j -ᵥ b i) = vectorSpan k (range b) by
        rw [this, ← direction_affineSpan, b.tot, AffineSubspace.direction_top]
      conv_rhs => rw [← image_univ]
      rw [vectorSpan_image_eq_span_vsub_set_right_ne k b (mem_univ i)]
      congr
      ext v
      simp)

@[simp]
/-
**AffineBasis.basisOf_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：basisOf_apply (i : ι) (j : { j : ι // j != i }) : b.basisOf i j = b ↑j -ᵥ 
b i
参数：i : ι；j : { j : ι // j != i }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisOf_apply (i : ι) (j : { j : ι // j ≠ i }) : b.basisOf i j = b ↑j -ᵥ b i := by
  simp [basisOf]

@[simp]
/-
**AffineBasis.basisOf_reindex** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：basisOf_reindex (i : ι') : (b.reindex e).basisOf i = (b.basisOf <| e.symm 
i).reindex (e.subtypeEquiv fun _ => e.eq_symm_apply.not)
参数：i : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.basisOf_apply`：basisOf_apply (i : ι) (j : { j : ι // j != i 
}) : b.basisOf i j = b ↑j -ᵥ b i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Equiv.subtypeEquiv_apply`：∀ {α : Sort u_1} {β : Sort u_4} {p : α → Prop}
 {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (e a))   (a : { a // p a }),
 (e.subtypeEqu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisOf_reindex (i : ι') :
    (b.reindex e).basisOf i =
      (b.basisOf <| e.symm i).reindex (e.subtypeEquiv fun _ => e.eq_symm_apply.not) := by
  ext j
  simp

/-- The `i`th barycentric coordinate of a point. -/
/-
**AffineBasis.coord** 是 Mathlib 中的一个定义，位于命名空间 `AffineBasis`。
形式化陈述：coord (i : ι) : P ->ᵃ[k] k where toFun q
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`th barycentric coordinate of a point.
-/
noncomputable def coord (i : ι) : P →ᵃ[k] k where
  toFun q := 1 - (b.basisOf i).sumCoords (q -ᵥ b i)
  linear := -(b.basisOf i).sumCoords
  map_vadd' q v := by
    rw [vadd_vsub_assoc, map_add, vadd_eq_add, LinearMap.neg_apply, sub_add_eq_sub_sub_swap,
      add_comm, sub_eq_add_neg]

@[simp]
/-
**AffineBasis.linear_eq_sumCoords** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：linear_eq_sumCoords (i : ι) : (b.coord i).linear = -(b.basisOf i).sumCoord
s
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linear_eq_sumCoords (i : ι) : (b.coord i).linear = -(b.basisOf i).sumCoords :=
  rfl

@[simp]
/-
**AffineBasis.coord_reindex** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：coord_reindex (i : ι') : (b.reindex e).coord i = b.coord (e.symm i)
参数：i : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `AffineBasis.basisOf_reindex`：basisOf_reindex (i : ι') : (b.reindex e).ba
sisOf i = (b.basisOf <| e.symm i).reindex (e.subtypeEquiv fun _ => e.eq_symm_app
ly.not)
· 使用定理 `Module.Basis.sumCoords_reindex`：sumCoords_reindex : (b.reindex e).sumCoo
rds = b.sumCoords
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineMap.mk.congr_simp`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3
} {V2 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [
inst_2 : _roo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coord_reindex (i : ι') : (b.reindex e).coord i = b.coord (e.symm i) := by
  ext
  simp [AffineBasis.coord]

@[simp]
/-
**AffineBasis.coord_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：coord_apply_eq (i : ι) : b.coord i (b i) = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coord_apply_eq (i : ι) : b.coord i (b i) = 1 := by
  simp only [coord, Basis.coe_sumCoords, map_zero, sub_zero,
    AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]

@[simp]
/-
**AffineBasis.coord_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：coord_apply_ne (h : i != j) : b.coord i (b j) = 0
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.coord.eq_1`：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6} {
P : Type u_7} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring 
k] [inst_3 :…
· 使用定理 `AffineMap.coe_mk`：coe_mk (f : P1 -> P2) (linear add) : ((mk f linear add
 : P1 ->ᵃ[k] P2) : P1 -> P2) = f
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `AffineBasis.basisOf_apply`：basisOf_apply (i : ι) (j : { j : ι // j != i 
}) : b.basisOf i j = b ↑j -ᵥ b i
· 使用定理 `Module.Basis.sumCoords_self_apply`：sumCoords_self_apply : b.sumCoords (b
 i) = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem coord_apply_ne (h : i ≠ j) : b.coord i (b j) = 0 := by
  rw [coord, AffineMap.coe_mk, ← Subtype.coe_mk (p := (· ≠ i)) j h.symm, ← b.basisOf_apply,
    Basis.sumCoords_self_apply, sub_self]
/-
**AffineBasis.coord_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：coord_apply [DecidableEq ι] (i j : ι) : b.coord i (b j) = if i = j then 1 
else 0
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineBasis.coord_apply_eq`：coord_apply_eq (i : ι) : b.coord i (b i) = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineBasis.coord_apply_ne`：coord_apply_ne (h : i != j) : b.coord i (b j
) = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem coord_apply [DecidableEq ι] (i j : ι) : b.coord i (b j) = if i = j then 1 else 0 := by
  rcases eq_or_ne i j with h | h <;> simp [h]

@[simp]
/-
**AffineBasis.coord_apply_combination_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineBa
sis`。
形式化陈述：coord_apply_combination_of_mem (hi : i in s) {w : ι -> k} (hw : s.sum w = 
1) : b.coord i (s.affineCombination k b w) = w i
参数：hi : i in s；hw : s.sum w = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `Finset.affineCombination_eq_linear_combination`：affineCombination_eq_lin
ear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k) (hw : ∑ i in s, w i = 1
) : s.affineCombination k p w = ∑ i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AffineBasis.coord_apply`：coord_apply [DecidableEq ι] (i j : ι) : b.coord
 i (b j) = if i = j then 1 else 0
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
-/
theorem coord_apply_combination_of_mem (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = w i := by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_true,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]
/-
**AffineBasis.coord_apply_combination_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eBasis`。
形式化陈述：coord_apply_combination_of_notMem (hi : i ∉ s) {w : ι -> k} (hw : s.sum w 
= 1) : b.coord i (s.affineCombination k b w) = 0
参数：hi : i ∉ s；hw : s.sum w = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `Finset.affineCombination_eq_linear_combination`：affineCombination_eq_lin
ear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k) (hw : ∑ i in s, w i = 1
) : s.affineCombination k p w = ∑ i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AffineBasis.coord_apply`：coord_apply [DecidableEq ι] (i j : ι) : b.coord
 i (b j) = if i = j then 1 else 0
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
-/
theorem coord_apply_combination_of_notMem (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = 0 := by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]
/-
**AffineBasis.sum_coord_apply_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：sum_coord_apply_eq_one [Fintype ι] (q : P) : ∑ i, b.coord i q = 1
参数：q : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.tot`：tot : affineSpan k (range b) = ⊤
· 使用定理 `AffineSubspace.mem_top`：mem_top (p : P) : p in (⊤ : AffineSubspace k P)
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AffineBasis.coord_apply_combination_of_mem`：coord_apply_combination_of_m
em (hi : i in s) {w : ι -> k} (hw : s.sum w = 1) : b.coord i (s.affineCombinatio
n k b w) = w i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem sum_coord_apply_eq_one [Fintype ι] (q : P) : ∑ i, b.coord i q = 1 := by
  have hq : q ∈ affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  convert! hw
  exact b.coord_apply_combination_of_mem (Finset.mem_univ _) hw

@[simp]
/-
**AffineBasis.affineCombination_coord_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineB
asis`。
形式化陈述：affineCombination_coord_eq_self [Fintype ι] (q : P) : (Finset.univ.affineC
ombination k b fun i => b.coord i q) = q
参数：q : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.tot`：tot : affineSpan k (range b) = ⊤
· 使用定理 `AffineSubspace.mem_top`：mem_top (p : P) : p in (⊤ : AffineSubspace k P)
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineBasis.coord_apply_combination_of_mem`：coord_apply_combination_of_m
em (hi : i in s) {w : ι -> k} (hw : s.sum w = 1) : b.coord i (s.affineCombinatio
n k b w) = w i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem affineCombination_coord_eq_self [Fintype ι] (q : P) :
    (Finset.univ.affineCombination k b fun i => b.coord i q) = q := by
  have hq : q ∈ affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  congr
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw

/-- A variant of `AffineBasis.affineCombination_coord_eq_self` for the special case when the
affine space is a module so we can talk about linear combinations. -/
@[simp]
/-
**AffineBasis.linear_combination_coord_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Basis`。
形式化陈述：linear_combination_coord_eq_self [Fintype ι] (b : AffineBasis ι k V) (v : 
V) : ∑ i, b.coord i v • b i = v
参数：b : AffineBasis ι k V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.affineCombination_coord_eq_self`：affineCombination_coord_eq_
self [Fintype ι] (q : P) : (Finset.univ.affineCombination k b fun i => b.coord i
 q) = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_eq_linear_combination`：affineCombination_eq_lin
ear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k) (hw : ∑ i in s, w i = 1
) : s.affineCombination k p w = ∑ i …
· 使用定理 `AffineBasis.sum_coord_apply_eq_one`：sum_coord_apply_eq_one [Fintype ι] (
q : P) : ∑ i, b.coord i q = 1

--- 原说明 ---
A variant of `AffineBasis.affineCombination_coord_eq_self` for the special case 
when the
affine space is a module so we can talk about linear combinations.
-/
theorem linear_combination_coord_eq_self [Fintype ι] (b : AffineBasis ι k V) (v : V) :
    ∑ i, b.coord i v • b i = v := by
  have hb := b.affineCombination_coord_eq_self v
  rwa [Finset.univ.affineCombination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one v)] at hb
/-
**AffineBasis.ext_elem** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：ext_elem [Finite ι] {q₁ q₂ : P} (h : forall i, b.coord i q₁ = b.coord i q₂
) : q₁ = q₂
参数：h : forall i, b.coord i q₁ = b.coord i q₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineBasis.affineCombination_coord_eq_self`：affineCombination_coord_eq_
self [Fintype ι] (q : P) : (Finset.univ.affineCombination k b fun i => b.coord i
 q) = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ext_elem [Finite ι] {q₁ q₂ : P} (h : ∀ i, b.coord i q₁ = b.coord i q₂) : q₁ = q₂ := by
  cases nonempty_fintype ι
  rw [← b.affineCombination_coord_eq_self q₁, ← b.affineCombination_coord_eq_self q₂]
  simp only [h]

@[simp]
/-
**AffineBasis.coe_coord_of_subsingleton_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Basis`。
形式化陈述：coe_coord_of_subsingleton_eq_one [Subsingleton ι] (i : ι) : (b.coord i : P
 -> k) = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
· 使用定理 `Set.subsingleton_of_subsingleton`：subsingleton_of_subsingleton [Subsingl
eton α] {s : Set α} : s.Subsingleton
· 使用定理 `AffineSubspace.subsingleton_of_subsingleton_span_eq_top`：subsingleton_of
_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton) (h₂ : affineSpan k s
 = ⊤) : Subsingleton P
· 使用定理 `AffineBasis.tot`：tot : affineSpan k (range b) = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用定理 `AffineBasis.coord_apply_combination_of_mem`：coord_apply_combination_of_m
em (hi : i in s) {w : ι -> k} (hw : s.sum w = 1) : b.coord i (s.affineCombinatio
n k b w) = w i
· 使用定理 `Function.const_apply`：∀ {β : Sort u_1} {α : Sort u_2} {y : β} {x : α}, F
unction.const α y x = y
-/
theorem coe_coord_of_subsingleton_eq_one [Subsingleton ι] (i : ι) : (b.coord i : P → k) = 1 := by
  ext q
  have hp : (range b).Subsingleton := by
    rw [← image_univ]
    apply Subsingleton.image
    apply subsingleton_of_subsingleton
  have := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hp b.tot
  let s : Finset ι := {i}
  have hi : i ∈ s := by simp [s]
  have hw : s.sum (Function.const ι (1 : k)) = 1 := by simp [s]
  have hq : q = s.affineCombination k b (Function.const ι (1 : k)) := by
    simp [eq_iff_true_of_subsingleton]
  rw [Pi.one_apply, hq, b.coord_apply_combination_of_mem hi hw, Function.const_apply]
/-
**AffineBasis.surjective_coord** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective b.coord i
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.filter_false_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `AffineBasis.coord_apply_combination_of_mem`：coord_apply_combination_of_m
em (hi : i in s) {w : ι -> k} (hw : s.sum w = 1) : b.coord i (s.affineCombinatio
n k b w) = w i
-/
theorem surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective <| b.coord i := by
  classical
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i ∈ s := by simp [s]
    let w : ι → k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [s, w, Finset.sum_ite, Finset.filter_insert, hij,
      Finset.filter_true_of_mem, Finset.filter_false_of_mem]
    use s.affineCombination k b w
    simp [w, b.coord_apply_combination_of_mem hi hw]

/-- Barycentric coordinates as an affine map. -/
/-
**AffineBasis.coords** 是 Mathlib 中的一个定义，位于命名空间 `AffineBasis`。
形式化陈述：coords : P ->ᵃ[k] ι -> k where toFun q i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Barycentric coordinates as an affine map.
-/
noncomputable def coords : P →ᵃ[k] ι → k where
  toFun q i := b.coord i q
  linear :=
    { toFun := fun v i => -(b.basisOf i).sumCoords v
      map_add' := fun v w => by ext; simp only [map_add, Pi.add_apply, neg_add]
      map_smul' := fun t v => by ext; simp }
  map_vadd' p v := by ext; simp

@[simp]
/-
**AffineBasis.coords_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：coords_apply (q : P) (i : ι) : b.coords q i = b.coord i q
参数：q : P；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coords_apply (q : P) (i : ι) : b.coords q i = b.coord i q :=
  rfl
/-
**AffineBasis.instVAdd** 是 Mathlib 中的一个实例，位于命名空间 `AffineBasis`。
形式化陈述：instVAdd : VAdd V (AffineBasis ι k P) where vadd x b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instVAdd : VAdd V (AffineBasis ι k P) where
  vadd x b :=
    { toFun := x +ᵥ ⇑b,
      ind' := b.ind'.vadd,
      tot' := by rw [Pi.vadd_def, ← vadd_set_range, ← AffineSubspace.pointwise_vadd_span, b.tot,
        AffineSubspace.pointwise_vadd_top] }
/-
**AffineBasis.coe_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6} {P : Type u_7} [inst : AddC
ommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k] [inst_3 : _root_.Module
 k V] (v : V) (b : AffineBasis ι k P), ⇑(v +ᵥ b) = v +ᵥ ⇑b
参数：v : V；b : AffineBasis ι k P；v +ᵥ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_vadd (v : V) (b : AffineBasis ι k P) : ⇑(v +ᵥ b) = v +ᵥ ⇑b := rfl
/-
**AffineBasis.basisOf_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6} {P : Type u_7} [inst : AddC
ommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k] [inst_3 : _root_.Module
 k V] (v : V) (b : AffineBasis ι k P), (v +ᵥ b).basisOf = b.basisOf
参数：v : V；b : AffineBasis ι k P；v +ᵥ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.basisOf_apply`：basisOf_apply (i : ι) (j : { j : ι // j != i 
}) : b.basisOf i j = b ↑j -ᵥ b i
· 使用定理 `vadd_vsub_vadd_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddC
ommGroup G] [inst_1 : AddTorsor G P] (v : G) (p₁ p₂ : P),   (v +ᵥ p₁) -ᵥ (v +ᵥ p
₂) = p₁ -ᵥ p₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma basisOf_vadd (v : V) (b : AffineBasis ι k P) : (v +ᵥ b).basisOf = b.basisOf := by
  ext
  simp
/-
**AffineBasis.instAddAction** 是 Mathlib 中的一个实例，位于命名空间 `AffineBasis`。
形式化陈述：instAddAction : AddAction V (AffineBasis ι k P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.coe_vadd`：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6} {P 
: Type u_7} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k]
 [inst_3 :…
-/
instance instAddAction : AddAction V (AffineBasis ι k P) :=
  DFunLike.coe_injective.addAction _ coe_vadd
/-
**AffineBasis.coord_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6} {P : Type u_7} [inst : AddC
ommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k] [inst_3 : _root_.Module
 k V] {i : ι} (v : V) (b : AffineBasis ι k P),   (v +ᵥ b).coord i = (b.coord i).
comp ↑(AffineEquiv.constVAdd k P v).symm
参数：v : V；b : AffineBasis ι k P；v +ᵥ b；b.coord i；AffineEquiv.constVAdd k P v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AffineBasis.basisOf_vadd`：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6}
 {P : Type u_7} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Rin
g k] [inst_3 :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineMap.mk.congr_simp`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3
} {V2 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [
inst_2 : _roo…
· 使用定理 `AffineEquiv.constVAdd_symm`：constVAdd_symm (v : V₁) : (constVAdd k P₁ v)
.symm = constVAdd k P₁ (-v)
· 使用定理 `AffineEquiv.constVAdd_apply`：∀ (k : Type u_1) (P₁ : Type u_2) {V₁ : Type
 u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module k V₁]
 [inst_3 : AddTor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
-/
@[simp] lemma coord_vadd (v : V) (b : AffineBasis ι k P) :
    (v +ᵥ b).coord i = (b.coord i).comp (AffineEquiv.constVAdd k P v).symm := by
  ext p
  simp only [coord, ne_eq, basisOf_vadd, coe_vadd, Pi.vadd_apply, Basis.coe_sumCoords,
    AffineMap.coe_mk, AffineEquiv.constVAdd_symm, AffineMap.coe_comp, AffineEquiv.coe_toAffineMap,
    Function.comp_apply, AffineEquiv.constVAdd_apply, sub_right_inj]
  congr! 1
  rw [vadd_vsub_assoc, neg_add_eq_sub, vsub_vadd_eq_vsub_sub]

section SMul
variable [Group G] [Group G']
variable [DistribMulAction G V] [DistribMulAction G' V]
variable [SMulCommClass G k V] [SMulCommClass G' k V]

/-- In an affine space that is also a vector space, an `AffineBasis` can be scaled.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts on `P` with a `VAdd`
version of a `DistribMulAction`. -/
/-
**AffineBasis.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `AffineBasis`。
形式化陈述：instSMul : SMul G (AffineBasis ι k V) where smul a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an affine space that is also a vector space, an `AffineBasis` can be scaled.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts o
n `P` with a `VAdd`
version of a `DistribMulAction`.
-/
instance instSMul : SMul G (AffineBasis ι k V) where
  smul a b :=
    { toFun := a • ⇑b,
      ind' := b.ind'.smul,
      tot' := by
        rw [Pi.smul_def, ← smul_set_range, ← AffineSubspace.smul_span, b.tot,
          AffineSubspace.smul_top (Group.isUnit a)] }
/-
**AffineBasis.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_3} {k : Type u_5} {V : Type u_6} [inst : AddC
ommGroup V] [inst_1 : Ring k]   [inst_2 : _root_.Module k V] [inst_3 : Group G] 
[inst_4 : DistribMulAction G V] [inst_5 : SMulCommClass G k V] (a : G)   (b : Af
fineBasis ι k V), ⇑(a • b) = a • ⇑b
参数：a : G；b : AffineBasis ι k V；a • b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_smul (a : G) (b : AffineBasis ι k V) : ⇑(a • b) = a • ⇑b := rfl

/-- TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
/-
**AffineBasis.** 是 Mathlib 中的一个实例，位于命名空间 `AffineBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts o
n `P` with a
`VAdd` version of a `DistribMulAction`.
-/
instance [SMulCommClass G G' V] : SMulCommClass G G' (AffineBasis ι k V) where
  smul_comm _g _g' _b := DFunLike.ext _ _ fun _ => smul_comm _ _ _

/-- TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
/-
**AffineBasis.** 是 Mathlib 中的一个实例，位于命名空间 `AffineBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts o
n `P` with a
`VAdd` version of a `DistribMulAction`.
-/
instance [SMul G G'] [IsScalarTower G G' V] : IsScalarTower G G' (AffineBasis ι k V) where
  smul_assoc _g _g' _b := DFunLike.ext _ _ fun _ => smul_assoc _ _ _
/-
**AffineBasis.basisOf_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_3} {k : Type u_5} {V : Type u_6} [inst : AddC
ommGroup V] [inst_1 : Ring k]   [inst_2 : _root_.Module k V] [inst_3 : Group G] 
[inst_4 : DistribMulAction G V] [inst_5 : SMulCommClass G k V] (a : G)   (b : Af
fineBasis ι k V) (i : ι), (a • b).basisOf i = a • b.basisOf i
参数：a : G；b : AffineBasis ι k V；i : ι；a • b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.basisOf_apply`：basisOf_apply (i : ι) (j : { j : ι // j != i 
}) : b.basisOf i j = b ↑j -ᵥ b i
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma basisOf_smul (a : G) (b : AffineBasis ι k V) (i : ι) :
    (a • b).basisOf i = a • b.basisOf i := by ext j; simp [smul_sub]
/-
**AffineBasis.reindex_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {G : Type u_3} {k : Type u_5} {V : Type u
_6} [inst : AddCommGroup V] [inst_1 : Ring k]   [inst_2 : _root_.Module k V] [in
st_3 : Group G] [inst_4 : DistribMulAction G V] [inst_5 : SMulCommClass G k V] (
a : G)   (b : AffineBasis ι k V) (e : ι ≃ ι'), (a • b).reindex e = a • b.reindex
 e
参数：a : G；b : AffineBasis ι k V；e : ι ≃ ι'；a • b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma reindex_smul (a : G) (b : AffineBasis ι k V) (e : ι ≃ ι') :
    (a • b).reindex e = a • b.reindex e :=
  rfl
/-
**AffineBasis.coord_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_3} {k : Type u_5} {V : Type u_6} [inst : AddC
ommGroup V] [inst_1 : Ring k]   [inst_2 : _root_.Module k V] [inst_3 : Group G] 
[inst_4 : DistribMulAction G V] [inst_5 : SMulCommClass G k V] (a : G)   (b : Af
fineBasis ι k V) (i : ι),   (a • b).coord i = (b.coord i).comp (↑(DistribMulActi
on.toLinearEquiv k V a).symm).toAffineMap
参数：a : G；b : AffineBasis ι k V；i : ι；a • b；b.coord i；↑(DistribMulAction.toLinear
Equiv k V a).symm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineBasis.basisOf_smul`：∀ {ι : Type u_1} {G : Type u_3} {k : Type u_5}
 {V : Type u_6} [inst : AddCommGroup V] [inst_1 : Ring k]   [inst_2 : _root_.Mod
ule k V] [inst…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `DistribMulAction.toLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
4} (M : Type u_5) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _ro
ot_.Module R M] [inst_3 : Group…
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `AffineMap.mk.congr_simp`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3
} {V2 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [
inst_2 : _roo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coord_smul (a : G) (b : AffineBasis ι k V) (i : ι) :
    (a • b).coord i = (b.coord i).comp (DistribMulAction.toLinearEquiv _ _ a).symm.toAffineMap := by
  ext v; simp [map_sub, coord]

/-- TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
/-
**AffineBasis.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `AffineBasis`。
形式化陈述：instMulAction : MulAction G (AffineBasis ι k V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.coe_smul`：∀ {ι : Type u_1} {G : Type u_3} {k : Type u_5} {V 
: Type u_6} [inst : AddCommGroup V] [inst_1 : Ring k]   [inst_2 : _root_.Module 
k V] [inst…

--- 原说明 ---
TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts o
n `P` with a
`VAdd` version of a `DistribMulAction`.
-/
instance instMulAction : MulAction G (AffineBasis ι k V) :=
  DFunLike.coe_injective.mulAction _ coe_smul

end SMul
end Ring

section DivisionRing

variable [DivisionRing k] [Module k V]

@[simp]
/-
**AffineBasis.coord_apply_centroid** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：coord_apply_centroid [CharZero k] (b : AffineBasis ι k P) {s : Finset ι} {
i : ι} (hi : i in s) : b.coord i (s.centroid k b) = (s.card : k)⁻¹
参数：b : AffineBasis ι k P；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centroid.eq_1`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [in
st : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [i
nst_3 : Ad…
· 使用定理 `AffineBasis.coord_apply_combination_of_mem`：coord_apply_combination_of_m
em (hi : i in s) {w : ι -> k} (hw : s.sum w = 1) : b.coord i (s.affineCombinatio
n k b w) = w i
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_nonempty`：sum_centroidWeights_eq_on
e_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i in s, s.centroidWeights k i = 
1
· 使用定理 `Finset.centroidWeights.eq_1`：∀ (k : Type u_1) [inst : DivisionRing k] {ι
 : Type u_4} (s : Finset ι),   Finset.centroidWeights k s = Function.const ι (↑s
.card)⁻¹
· 使用定理 `Function.const_apply`：∀ {β : Sort u_1} {α : Sort u_2} {y : β} {x : α}, F
unction.const α y x = y
-/
theorem coord_apply_centroid [CharZero k] (b : AffineBasis ι k P) {s : Finset ι} {i : ι}
    (hi : i ∈ s) : b.coord i (s.centroid k b) = (s.card : k)⁻¹ := by
  rw [Finset.centroid,
    b.coord_apply_combination_of_mem hi (s.sum_centroidWeights_eq_one_of_nonempty _ ⟨i, hi⟩),
    Finset.centroidWeights, Function.const_apply]
/-
**AffineBasis.exists_affine_subbasis** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：exists_affine_subbasis {t : Set P} (ht : affineSpan k t = ⊤) : exists s su
bseteq t, exists b : AffineBasis s k P, ⇑b = ((↑) : s -> P)
参数：ht : affineSpan k t = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_affineIndependent`：exists_affineIndependent (s : Set P) : exists 
t subseteq s, affineSpan k t = affineSpan k s ∧ AffineIndependent k ((↑) : t -> 
P)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem exists_affine_subbasis {t : Set P} (ht : affineSpan k t = ⊤) :
    ∃ s ⊆ t, ∃ b : AffineBasis s k P, ⇑b = ((↑) : s → P) := by
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affineIndependent k V t
  refine ⟨s, hst, ⟨(↑), h_ind, ?_⟩, rfl⟩
  rw [Subtype.range_coe, h_tot, ht]

variable (k V P)
/-
**AffineBasis.exists_affineBasis** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：exists_affineBasis : exists (s : Set P) (b : AffineBasis (↥s) k P), ⇑b = (
(↑) : s -> P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.exists_affine_subbasis`：exists_affine_subbasis {t : Set P} (
ht : affineSpan k t = ⊤) : exists s subseteq t, exists b : AffineBasis s k P, ⇑b
 = ((↑) : s -> P)
· 使用定理 `AffineSubspace.span_univ`：span_univ : affineSpan k (Set.univ : Set P) = 
⊤
-/
theorem exists_affineBasis : ∃ (s : Set P) (b : AffineBasis (↥s) k P), ⇑b = ((↑) : s → P) :=
  let ⟨s, _, hs⟩ := exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩

end DivisionRing

end AffineBasis

