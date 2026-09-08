/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Ramification of infinite places of a number field

This file studies the ramification of infinite places of a number field.

## Main Definitions and Results

* `NumberField.InfinitePlace.comap`: the restriction of an infinite place along an embedding.
* `NumberField.InfinitePlace.orbitRelEquiv`: the equiv between the orbits of infinite places under
  the action of the Galois group and the infinite places of the base field.
* `NumberField.InfinitePlace.IsUnramified`: an infinite place is unramified in a field extension
  if the restriction has the same multiplicity.
* `NumberField.InfinitePlace.not_isUnramified_iff`: an infinite place is not unramified
  (i.e., is ramified) iff it is a complex place above a real place.
* `NumberField.InfinitePlace.IsUnramifiedIn`: an infinite place of the base field is unramified
  in a field extension if every infinite place over it is unramified.
* `IsUnramifiedAtInfinitePlaces`: a field extension is unramified at infinite places if every
  infinite place is unramified.

## Tags

number field, infinite places, ramification
-/

@[expose] public section

open NumberField Fintype Module ComplexEmbedding

namespace NumberField.InfinitePlace

open scoped Finset

variable {k : Type*} [Field k] {K : Type*} [Field K] {F : Type*} [Field F]

/-- The restriction of an infinite place along an embedding. -/
/-
**NumberField.InfinitePlace.comap** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Infinit
ePlace`。
形式化陈述：comap (w : InfinitePlace K) (f : k ->+* K) : InfinitePlace k
参数：w : InfinitePlace K；f : k ->+* K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of an infinite place along an embedding.
-/
def comap (w : InfinitePlace K) (f : k →+* K) : InfinitePlace k :=
  ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; change _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩

@[simp]
/-
**NumberField.InfinitePlace.comap_mk** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.Infi
nitePlace`。
形式化陈述：comap_mk (φ : K ->+* Complex) (f : k ->+* K) : (mk φ).comap f = mk (φ.comp
 f)
参数：φ : K ->+* Complex；f : k ->+* K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_mk (φ : K →+* ℂ) (f : k →+* K) : (mk φ).comap f = mk (φ.comp f) := rfl
/-
**NumberField.InfinitePlace.comap_id** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.Infi
nitePlace`。
形式化陈述：comap_id (w : InfinitePlace K) : w.comap (RingHom.id K) = w
参数：w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_id (w : InfinitePlace K) : w.comap (RingHom.id K) = w := rfl
/-
**NumberField.InfinitePlace.comap_comp** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.In
finitePlace`。
形式化陈述：comap_comp (w : InfinitePlace K) (f : F ->+* K) (g : k ->+* F) : w.comap (
f.comp g) = (w.comap f).comap g
参数：w : InfinitePlace K；f : F ->+* K；g : k ->+* F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_comp (w : InfinitePlace K) (f : F →+* K) (g : k →+* F) :
    w.comap (f.comp g) = (w.comap f).comap g := rfl

@[simp]
/-
**NumberField.InfinitePlace.comap_apply** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.I
nfinitePlace`。
形式化陈述：comap_apply (w : InfinitePlace K) (f : k ->+* K) (x : k) : w.comap f x = w
 (f x)
参数：w : InfinitePlace K；f : k ->+* K；x : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_apply (w : InfinitePlace K) (f : k →+* K) (x : k) :
    w.comap f x = w (f x) := rfl
/-
**NumberField.InfinitePlace.comp_of_comap_eq** 是 Mathlib 中的一个引理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：comp_of_comap_eq {v : InfinitePlace k} {w : InfinitePlace K} {f : k ->+* K
} (h : w.comap f = v) (x : k) : w (f x) = v x
参数：h : w.comap f = v；x : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_of_comap_eq {v : InfinitePlace k} {w : InfinitePlace K} {f : k →+* K}
    (h : w.comap f = v) (x : k) : w (f x) = v x := by
  simp [← h]
/-
**NumberField.InfinitePlace.coe_mk_comp** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.I
nfinitePlace`。
形式化陈述：coe_mk_comp {ψ : K ->+* Complex} {f : k ->+* K} (h : Function.Injective f)
 : (mk (ψ.comp f)).1 = (mk ψ).1.comp h
参数：h : Function.Injective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk_comp {ψ : K →+* ℂ} {f : k →+* K}
    (h : Function.Injective f) : (mk (ψ.comp f)).1 = (mk ψ).1.comp h := rfl
/-
**NumberField.InfinitePlace.comap_mk_lift** 是 Mathlib 中的一个引理，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：comap_mk_lift [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex)
 : (mk (ComplexEmbedding.lift K φ)).comap (algebraMap k K) = mk φ
参数：φ : k ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.ComplexEmbedding.lift_comp_algebraMap`：lift_comp_algebraMap 
[Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) : (lift K φ).comp (
algebraMap k K) = φ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_mk_lift [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k →+* ℂ) :
    (mk (ComplexEmbedding.lift K φ)).comap (algebraMap k K) = mk φ := by simp
/-
**NumberField.InfinitePlace.IsReal.comap** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
InfinitePlace.IsReal`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] (f : k
 →+* K) {w : NumberField.InfinitePlace K},   w.IsReal → (w.comap f).IsReal
参数：f : k →+* K；w.comap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
· 使用定理 `NumberField.ComplexEmbedding.IsReal.comp`：∀ {K : Type u_1} [inst : Field
 K] {k : Type u_2} [inst_1 : Field k] (f : k →+* K) {φ : K →+* ℂ},   NumberField
.ComplexEmbedding.IsReal φ → N…
-/
lemma IsReal.comap (f : k →+* K) {w : InfinitePlace K} (hφ : IsReal w) :
    IsReal (w.comap f) := by
  rw [← mk_embedding w, comap_mk, isReal_mk_iff]
  rw [← mk_embedding w, isReal_mk_iff] at hφ
  exact hφ.comp f
/-
**NumberField.InfinitePlace.IsComplex.of_comap** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.InfinitePlace.IsComplex`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] (f : k
 →+* K) {w : NumberField.InfinitePlace K},   (w.comap f).IsComplex → w.IsComplex
参数：f : k →+* K；w.comap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `NumberField.InfinitePlace.IsReal.comap`：∀ {k : Type u_1} [inst : Field k
] {K : Type u_2} [inst_1 : Field K] (f : k →+* K) {w : NumberField.InfinitePlace
 K},   w.IsReal → (w.comap f…
-/
lemma IsComplex.of_comap (f : k →+* K) {w : InfinitePlace K} (hf : IsComplex (w.comap f)) :
    IsComplex w := by
  rw [← not_isReal_iff_isComplex] at hf ⊢
  exact (IsReal.comap f).mt hf
/-
**NumberField.InfinitePlace.isReal_comap_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：isReal_comap_iff (f : k ≃+* K) {w : InfinitePlace K} : IsReal (w.comap (f 
: k ->+* K)) ↔ IsReal w
参数：f : k ≃+* K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
· 使用引理 `NumberField.ComplexEmbedding.isReal_comp_iff`：isReal_comp_iff {f : k ≃+*
 K} {φ : K ->+* Complex} : IsReal (φ.comp (f : k ->+* K)) ↔ IsReal φ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isReal_comap_iff (f : k ≃+* K) {w : InfinitePlace K} :
    IsReal (w.comap (f : k →+* K)) ↔ IsReal w := by
  rw [← mk_embedding w, comap_mk, isReal_mk_iff, isReal_mk_iff, ComplexEmbedding.isReal_comp_iff]
/-
**NumberField.InfinitePlace.comap_surjective** 是 Mathlib 中的一个引理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：comap_surjective [Algebra k K] [Algebra.IsAlgebraic k K] : Function.Surjec
tive (comap · (algebraMap k K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.ComplexEmbedding.lift_comp_algebraMap`：lift_comp_algebraMap 
[Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) : (lift K φ).comp (
algebraMap k K) = φ
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_surjective [Algebra k K] [Algebra.IsAlgebraic k K] :
    Function.Surjective (comap · (algebraMap k K)) := fun w ↦
  ⟨(mk (ComplexEmbedding.lift K  w.embedding)), by simp⟩
/-
**NumberField.InfinitePlace.comap_embedding_of_isReal** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
形式化陈述：comap_embedding_of_isReal (f : k ->+* K) {w : InfinitePlace K} (h : (w.com
ap f).IsReal) : (w.comap f).embedding = w.embedding.comp f
参数：f : k ->+* K；h : (w.comap f).IsReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq_of_isReal`：embedding_mk_eq_of_
isReal {φ : K ->+* Complex} (h : ComplexEmbedding.IsReal φ) : embedding (mk φ) =
 φ
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
-/
theorem comap_embedding_of_isReal (f : k →+* K) {w : InfinitePlace K} (h : (w.comap f).IsReal) :
    (w.comap f).embedding = w.embedding.comp f := by
   rw [← mk_embedding w, comap_mk, mk_embedding, embedding_mk_eq_of_isReal
    (by rwa [← isReal_mk_iff, ← comap_mk, mk_embedding])]
/-
**NumberField.InfinitePlace.mult_comap_le** 是 Mathlib 中的一个引理，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：mult_comap_le (f : k ->+* K) (w : InfinitePlace K) : mult (w.comap f) <= m
ult w
参数：f : k ->+* K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.mult.eq_1`：∀ {K : Type u_1} [inst : Field K] (
w : NumberField.InfinitePlace K), w.mult = if w.IsReal then 1 else 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `NumberField.InfinitePlace.IsReal.comap`：∀ {k : Type u_1} [inst : Field k
] {K : Type u_2} [inst_1 : Field K] (f : k →+* K) {w : NumberField.InfinitePlace
 K},   w.IsReal → (w.comap f…
-/
lemma mult_comap_le (f : k →+* K) (w : InfinitePlace K) : mult (w.comap f) ≤ mult w := by
  rw [mult, mult]
  split_ifs with h₁ h₂ h₂
  pick_goal 3
  · exact (h₁ (h₂.comap _)).elim
  all_goals decide

variable [Algebra k K] (σ : Gal(K/k)) (w : InfinitePlace K)
variable (k K)
/-
**NumberField.InfinitePlace.card_mono** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.Inf
initePlace`。
形式化陈述：card_mono [NumberField k] [NumberField K] : card (InfinitePlace k) <= card
 (InfinitePlace K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Fintype.card_le_of_surjective`：card_le_of_surjective (f : α -> β) (h : F
unction.Surjective f) : card β <= card α
· 使用引理 `NumberField.InfinitePlace.comap_surjective`：comap_surjective [Algebra k 
K] [Algebra.IsAlgebraic k K] : Function.Surjective (comap · (algebraMap k K))
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma card_mono [NumberField k] [NumberField K] :
    card (InfinitePlace k) ≤ card (InfinitePlace K) :=
  have := Module.Finite.of_restrictScalars_finite ℚ k K
  Fintype.card_le_of_surjective _ comap_surjective

variable {k K}

/-- The action of the Galois group on infinite places. -/
@[simps! smul_coe_apply]
/-
**NumberField.InfinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.InfinitePlac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the Galois group on infinite places.
-/
instance : MulAction Gal(K/k) (InfinitePlace K) where
  smul := fun σ w ↦ w.comap σ.symm
  one_smul := fun _ ↦ rfl
  mul_smul := fun _ _ _ ↦ rfl
/-
**NumberField.InfinitePlace.smul_eq_comap** 是 Mathlib 中的一个引理，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：smul_eq_comap : σ • w = w.comap σ.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_eq_comap : σ • w = w.comap σ.symm := rfl
/-
**NumberField.InfinitePlace.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.In
finitePlace`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K] (σ : Gal(K/k))   (w : NumberField.InfinitePlace K) (x : K), (σ 
• w) x = w (σ.symm x)
参数：σ : Gal(K/k)；w : NumberField.InfinitePlace K；x : K；σ • w；σ.symm x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_apply (x) : (σ • w) x = w (σ.symm x) := rfl
/-
**NumberField.InfinitePlace.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Infin
itePlace`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K] (σ : Gal(K/k)) (φ : K →+* ℂ),   σ • NumberField.InfinitePlace.m
k φ = NumberField.InfinitePlace.mk (φ.comp ↑σ.symm)
参数：σ : Gal(K/k)；φ : K →+* ℂ；φ.comp ↑σ.symm。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_mk (φ : K →+* ℂ) : σ • mk φ = mk (φ.comp σ.symm) := rfl
/-
**NumberField.InfinitePlace.comap_smul** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.In
finitePlace`。
形式化陈述：comap_smul {f : F ->+* K} : (σ • w).comap f = w.comap (RingHom.comp σ.symm
 f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_smul {f : F →+* K} : (σ • w).comap f = w.comap (RingHom.comp σ.symm f) := rfl

variable {σ w}
/-
**NumberField.InfinitePlace.isReal_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberFie
ld.InfinitePlace`。
形式化陈述：isReal_smul_iff : IsReal (σ • w) ↔ IsReal w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.isReal_comap_iff`：isReal_comap_iff (f : k ≃+* 
K) {w : InfinitePlace K} : IsReal (w.comap (f : k ->+* K)) ↔ IsReal w
-/
lemma isReal_smul_iff : IsReal (σ • w) ↔ IsReal w := isReal_comap_iff (f := σ.symm.toRingEquiv)
/-
**NumberField.InfinitePlace.isComplex_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Number
Field.InfinitePlace`。
形式化陈述：isComplex_smul_iff : IsComplex (σ • w) ↔ IsComplex w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用引理 `NumberField.InfinitePlace.isReal_smul_iff`：isReal_smul_iff : IsReal (σ •
 w) ↔ IsReal w
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isComplex_smul_iff : IsComplex (σ • w) ↔ IsComplex w := by
  rw [← not_isReal_iff_isComplex, ← not_isReal_iff_isComplex, isReal_smul_iff]
/-
**NumberField.InfinitePlace.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq** 是 
Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.ComplexEmbedding`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K] [IsGalois k K]   (φ ψ : K →+* ℂ), φ.comp (algebraMap k K) = ψ.c
omp (algebraMap k K) → ∃ σ, φ.comp ↑σ.symm = ψ
参数：φ ψ : K →+* ℂ；algebraMap k K；algebraMap k K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`：exists_comp
_symm_eq_of_comp_eq [Algebra k K] [IsGalois k K] (φ ψ : K ->+* Complex) (h : φ.c
omp (algebraMap k K) = ψ.comp (algebraMap k K)) :…
-/
lemma ComplexEmbedding.exists_comp_symm_eq_of_comp_eq [IsGalois k K] (φ ψ : K →+* ℂ)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    ∃ σ : Gal(K/k), φ.comp σ.symm = ψ :=
  NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq φ ψ h
/-
**NumberField.InfinitePlace.exists_smul_eq_of_comap_eq** 是 Mathlib 中的一个引理，位于命名空间
 `NumberField.InfinitePlace`。
形式化陈述：exists_smul_eq_of_comap_eq [IsGalois k K] {w w' : InfinitePlace K} (h : w.
comap (algebraMap k K) = w'.comap (algebraMap k K)) : exists σ : Gal(K/k), σ • w
 = w'
参数：h : w.comap (algebraMap k K) = w'.comap (algebraMap k K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.mk_eq_iff`：mk_eq_iff {φ ψ : K ->+* Complex} : 
mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `NumberField.InfinitePlace.ComplexEmbedding.exists_comp_symm_eq_of_comp_e
q`：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 :
 Algebra k K] [IsGalois k K]   (φ ψ : K →+* ℂ), φ.comp (algebra…
· 使用定理 `NumberField.InfinitePlace.smul_mk`：∀ {k : Type u_1} [inst : Field k] {K 
: Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K] (σ : Gal(K/k)) (φ : K →+* 
ℂ),   σ • NumberField.I…
-/
lemma exists_smul_eq_of_comap_eq [IsGalois k K] {w w' : InfinitePlace K}
    (h : w.comap (algebraMap k K) = w'.comap (algebraMap k K)) : ∃ σ : Gal(K/k), σ • w = w' := by
  rw [← mk_embedding w, ← mk_embedding w', comap_mk, comap_mk, mk_eq_iff] at h
  cases h with
  | inl h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq w.embedding w'.embedding h
    use σ
    rw [← mk_embedding w, ← mk_embedding w', smul_mk, hσ]
  | inr h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      ((starRingEnd ℂ).comp (embedding w)) w'.embedding h
    use σ
    rw [← mk_embedding w, ← mk_embedding w', smul_mk, mk_eq_iff]
    exact Or.inr hσ
/-
**NumberField.InfinitePlace.mem_orbit_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：mem_orbit_iff [IsGalois k K] {w w' : InfinitePlace K} : w' in MulAction.or
bit Gal(K/k) w ↔ w.comap (algebraMap k K) = w'.comap (algebraMap k K)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `NumberField.InfinitePlace.smul_mk`：∀ {k : Type u_1} [inst : Field k] {K 
: Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K] (σ : Gal(K/k)) (φ : K →+* 
ℂ),   σ • NumberField.I…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `NumberField.InfinitePlace.exists_smul_eq_of_comap_eq`：exists_smul_eq_of_
comap_eq [IsGalois k K] {w w' : InfinitePlace K} (h : w.comap (algebraMap k K) =
 w'.comap (algebraMap k K)) : exists σ : G…
-/
lemma mem_orbit_iff [IsGalois k K] {w w' : InfinitePlace K} :
    w' ∈ MulAction.orbit Gal(K/k) w ↔ w.comap (algebraMap k K) = w'.comap (algebraMap k K) := by
  refine ⟨?_, exists_smul_eq_of_comap_eq⟩
  rintro ⟨σ, rfl : σ • w = w'⟩
  rw [← mk_embedding w, comap_mk, smul_mk, comap_mk]
  congr 1; ext1; simp

/-- The orbits of infinite places under the action of the Galois group are indexed by
the infinite places of the base field. -/
noncomputable
/-
**NumberField.InfinitePlace.orbitRelEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：orbitRelEquiv [IsGalois k K] : Quotient (MulAction.orbitRel Gal(K/k) (Infi
nitePlace K)) ≃ InfinitePlace k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def orbitRelEquiv [IsGalois k K] :
    Quotient (MulAction.orbitRel Gal(K/k) (InfinitePlace K)) ≃ InfinitePlace k := by
  refine Equiv.ofBijective (Quotient.lift (comap · (algebraMap k K))
    fun _ _ e ↦ (mem_orbit_iff.mp e).symm) ⟨?_, ?_⟩
  · rintro ⟨w⟩ ⟨w'⟩ e
    exact Quotient.sound (mem_orbit_iff.mpr e.symm)
  · intro w
    obtain ⟨w', hw⟩ := comap_surjective (K := K) w
    exact ⟨⟦w'⟧, hw⟩
/-
**NumberField.InfinitePlace.orbitRelEquiv_apply_mk''** 是 Mathlib 中的一个引理，位于命名空间 `
NumberField.InfinitePlace`。
形式化陈述：orbitRelEquiv_apply_mk'' [IsGalois k K] (w : InfinitePlace K) : orbitRelEq
uiv (Quotient.mk'' w) = comap w (algebraMap k K)
参数：w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
lemma orbitRelEquiv_apply_mk'' [IsGalois k K] (w : InfinitePlace K) :
    orbitRelEquiv (Quotient.mk'' w) = comap w (algebraMap k K) := rfl

variable (k w)

/--
An infinite place is unramified in a field extension if the restriction has the same multiplicity.
-/
/-
**NumberField.InfinitePlace.IsUnramified** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.
InfinitePlace`。
形式化陈述：IsUnramified : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite place is unramified in a field extension if the restriction has the 
same multiplicity.
-/
def IsUnramified : Prop := mult (w.comap (algebraMap k K)) = mult w

/--
An infinite place is ramified in a field extension if it is not unramified.
-/
/-
**NumberField.InfinitePlace.IsRamified** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField.
InfinitePlace`。
形式化陈述：IsRamified : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite place is ramified in a field extension if it is not unramified.
-/
abbrev IsRamified : Prop := ¬w.IsUnramified k
/-
**NumberField.InfinitePlace.isUnramified_or_isRamified** 是 Mathlib 中的一个引理，位于命名空间
 `NumberField.InfinitePlace`。
形式化陈述：isUnramified_or_isRamified : w.IsUnramified k ∨ w.IsRamified k
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_not`：or_not {p : Prop} : p ∨ ¬p
-/
lemma isUnramified_or_isRamified : w.IsUnramified k ∨ w.IsRamified k :=
  or_not

variable {k}
/-
**NumberField.InfinitePlace.isUnramified_self** 是 Mathlib 中的一个引理，位于命名空间 `NumberF
ield.InfinitePlace`。
形式化陈述：isUnramified_self : IsUnramified K w
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isUnramified_self : IsUnramified K w := rfl

variable {w}
/-
**NumberField.InfinitePlace.IsUnramified.eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.InfinitePlace.IsUnramified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K},   NumberField.InfinitePlac
e.IsUnramified k w → (w.comap (algebraMap k K)).mult = w.mult
参数：w.comap (algebraMap k K)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsUnramified.eq (h : IsUnramified k w) : mult (w.comap (algebraMap k K)) = mult w := h
/-
**NumberField.InfinitePlace.isUnramified_iff_mult_le** 是 Mathlib 中的一个引理，位于命名空间 `
NumberField.InfinitePlace`。
形式化陈述：isUnramified_iff_mult_le : IsUnramified k w ↔ mult w <= mult (w.comap (alg
ebraMap k K))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.IsUnramified.eq_1`：∀ (k : Type u_1) [inst : Fi
eld k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   (w : NumberFie
ld.InfinitePlace K),   NumberFiel…
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `NumberField.InfinitePlace.mult_comap_le`：mult_comap_le (f : k ->+* K) (w
 : InfinitePlace K) : mult (w.comap f) <= mult w
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isUnramified_iff_mult_le :
    IsUnramified k w ↔ mult w ≤ mult (w.comap (algebraMap k K)) := by
  rw [IsUnramified, le_antisymm_iff, and_iff_right]
  exact mult_comap_le _ _

variable [Algebra k F]
/-
**NumberField.InfinitePlace.IsUnramified.comap_algHom** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace.IsUnramified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] {F : T
ype u_3} [inst_2 : Field F]   [inst_3 : Algebra k K] [inst_4 : Algebra k F] {w :
 NumberField.InfinitePlace F},   NumberField.InfinitePlace.IsUnramified k w → ∀ 
(f : K →ₐ[k] F), NumberField.InfinitePlace.IsUnramified k (w.comap ↑f)
参数：f : K →ₐ[k] F；w.comap ↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff_mult_le`：isUnramified_iff_mul
t_le : IsUnramified k w ↔ mult w <= mult (w.comap (algebraMap k K))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NumberField.InfinitePlace.comap_comp`：comap_comp (w : InfinitePlace K) (
f : F ->+* K) (g : k ->+* F) : w.comap (f.comp g) = (w.comap f).comap g
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `NumberField.InfinitePlace.IsUnramified.eq`：∀ {k : Type u_1} [inst : Fiel
d k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : NumberField
.InfinitePlace K},   NumberFiel…
· 使用引理 `NumberField.InfinitePlace.mult_comap_le`：mult_comap_le (f : k ->+* K) (w
 : InfinitePlace K) : mult (w.comap f) <= mult w
-/
lemma IsUnramified.comap_algHom {w : InfinitePlace F} (h : IsUnramified k w) (f : K →ₐ[k] F) :
    IsUnramified k (w.comap (f : K →+* F)) := by
  rw [InfinitePlace.isUnramified_iff_mult_le, ← InfinitePlace.comap_comp, f.comp_algebraMap, h.eq]
  exact InfinitePlace.mult_comap_le _ _

variable (K)
variable [Algebra K F] [IsScalarTower k K F]
/-
**NumberField.InfinitePlace.IsUnramified.of_restrictScalars** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.InfinitePlace.IsUnramified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] (K : Type u_2) [inst_1 : Field K] {F : T
ype u_3} [inst_2 : Field F]   [inst_3 : Algebra k K] [inst_4 : Algebra k F] [ins
t_5 : Algebra K F] [IsScalarTower k K F]   {w : NumberField.InfinitePlace F},   
NumberField.InfinitePlace.IsUnramified k w → NumberField.InfinitePlace.IsUnramif
ied K w
参数：K : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff_mult_le`：isUnramified_iff_mul
t_le : IsUnramified k w ↔ mult w <= mult (w.comap (algebraMap k K))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.IsUnramified.eq`：∀ {k : Type u_1} [inst : Fiel
d k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : NumberField
.InfinitePlace K},   NumberFiel…
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用引理 `NumberField.InfinitePlace.comap_comp`：comap_comp (w : InfinitePlace K) (
f : F ->+* K) (g : k ->+* F) : w.comap (f.comp g) = (w.comap f).comap g
· 使用引理 `NumberField.InfinitePlace.mult_comap_le`：mult_comap_le (f : k ->+* K) (w
 : InfinitePlace K) : mult (w.comap f) <= mult w
-/
lemma IsUnramified.of_restrictScalars {w : InfinitePlace F} (h : IsUnramified k w) :
    IsUnramified K w := by
  rw [InfinitePlace.isUnramified_iff_mult_le, ← h.eq, IsScalarTower.algebraMap_eq k K F,
    InfinitePlace.comap_comp]
  exact InfinitePlace.mult_comap_le _ _
/-
**NumberField.InfinitePlace.IsUnramified.comap** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.InfinitePlace.IsUnramified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] (K : Type u_2) [inst_1 : Field K] {F : T
ype u_3} [inst_2 : Field F]   [inst_3 : Algebra k K] [inst_4 : Algebra k F] [ins
t_5 : Algebra K F] [IsScalarTower k K F]   {w : NumberField.InfinitePlace F},   
NumberField.InfinitePlace.IsUnramified k w → NumberField.InfinitePlace.IsUnramif
ied k (w.comap (algebraMap K F))
参数：K : Type u_2；w.comap (algebraMap K F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.IsUnramified.comap_algHom`：∀ {k : Type u_1} [i
nst : Field k] {K : Type u_2} [inst_1 : Field K] {F : Type u_3} [inst_2 : Field 
F]   [inst_3 : Algebra k K] [inst_4 : Alg…
-/
lemma IsUnramified.comap {w : InfinitePlace F} (h : IsUnramified k w) :
    IsUnramified k (w.comap (algebraMap K F)) :=
  h.comap_algHom (IsScalarTower.toAlgHom k K F)

variable {K}

/--
An infinite place is not unramified (i.e. ramified) iff it is a complex place above a real place.
-/
/-
**NumberField.InfinitePlace.not_isUnramified_iff** 是 Mathlib 中的一个引理，位于命名空间 `Numb
erField.InfinitePlace`。
形式化陈述：not_isUnramified_iff : ¬ IsUnramified k w ↔ IsComplex w ∧ IsReal (w.comap 
(algebraMap k K))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.IsUnramified.eq_1`：∀ (k : Type u_1) [inst : Fi
eld k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   (w : NumberFie
ld.InfinitePlace K),   NumberFiel…
· 使用定理 `NumberField.InfinitePlace.mult.eq_1`：∀ {K : Type u_1} [inst : Field K] (
w : NumberField.InfinitePlace K), w.mult = if w.IsReal then 1 else 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `NumberField.InfinitePlace.IsReal.comap`：∀ {k : Type u_1} [inst : Field k
] {K : Type u_2} [inst_1 : Field K] (f : k →+* K) {w : NumberField.InfinitePlace
 K},   w.IsReal → (w.comap f…

--- 原说明 ---
An infinite place is not unramified (i.e. ramified) iff it is a complex place ab
ove a real place.
-/
lemma not_isUnramified_iff :
    ¬ IsUnramified k w ↔ IsComplex w ∧ IsReal (w.comap (algebraMap k K)) := by
  rw [IsUnramified, mult, mult, ← not_isReal_iff_isComplex]
  split_ifs with h₁ h₂ h₂ <;>
    simp only [not_true_eq_false, false_iff, and_self, forall_true_left, IsEmpty.forall_iff,
      not_and, OfNat.one_ne_ofNat, not_false_eq_true, true_iff, OfNat.ofNat_ne_one, h₁, h₂]
  exact h₁ (h₂.comap _)
/-
**NumberField.InfinitePlace.isUnramified_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：isUnramified_iff : IsUnramified k w ↔ IsReal w ∨ IsComplex (w.comap (algeb
raMap k K))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `NumberField.InfinitePlace.not_isUnramified_iff`：not_isUnramified_iff : ¬
 IsUnramified k w ↔ IsComplex w ∧ IsReal (w.comap (algebraMap k K))
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `NumberField.InfinitePlace.not_isComplex_iff_isReal`：not_isComplex_iff_is
Real {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isUnramified_iff :
    IsUnramified k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K)) := by
  rw [← not_iff_not, not_isUnramified_iff, not_or,
    not_isReal_iff_isComplex, not_isComplex_iff_isReal]
/-
**NumberField.InfinitePlace.isRamified_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.InfinitePlace`。
形式化陈述：isRamified_iff : w.IsRamified k ↔ w.IsComplex ∧ (w.comap (algebraMap k K))
.IsReal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.not_isUnramified_iff`：not_isUnramified_iff : ¬
 IsUnramified k w ↔ IsComplex w ∧ IsReal (w.comap (algebraMap k K))
-/
theorem isRamified_iff : w.IsRamified k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal :=
  not_isUnramified_iff
/-
**NumberField.InfinitePlace.IsRamified.isComplex** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.InfinitePlace.IsRamified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K}, NumberField.InfinitePlace.
IsRamified k w → w.IsComplex
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isRamified_iff`：isRamified_iff : w.IsRamified 
k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
-/
theorem IsRamified.isComplex (h : w.IsRamified k) : w.IsComplex := (isRamified_iff.1 h).1
/-
**NumberField.InfinitePlace.IsRamified.isReal** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.InfinitePlace.IsRamified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K}, NumberField.InfinitePlace.
IsRamified k w → (w.comap (algebraMap k K)).IsReal
参数：w.comap (algebraMap k K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isRamified_iff`：isRamified_iff : w.IsRamified 
k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
-/
theorem IsRamified.isReal (h : w.IsRamified k) : (w.comap (algebraMap k K)).IsReal :=
  (isRamified_iff.1 h).2
/-
**NumberField.InfinitePlace.IsRamified.ne_conjugate** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.InfinitePlace.IsRamified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w₁ w₂ : NumberField.InfinitePlace K},   NumberField.Infinite
Place.IsRamified k w₂ → w₁.embedding ≠ NumberField.ComplexEmbedding.conjugate w₂
.embedding
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.isComplex_iff`：isComplex_iff {w : InfinitePlac
e K} : IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.InfinitePlace.isRamified_iff`：isRamified_iff : w.IsRamified 
k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `NumberField.InfinitePlace.mk_conjugate_eq`：mk_conjugate_eq (φ : K ->+* C
omplex) : mk (ComplexEmbedding.conjugate φ) = mk φ
-/
theorem IsRamified.ne_conjugate {w₁ w₂ : InfinitePlace K} (h : w₂.IsRamified k) :
    w₁.embedding ≠ ComplexEmbedding.conjugate w₂.embedding := by
  by_cases h_eq : w₁ = w₂
  · rw [isRamified_iff, isComplex_iff] at h
    exact Ne.symm (h_eq ▸ h.1)
  · contrapose h_eq
    rw [← mk_embedding w₁, h_eq, mk_conjugate_eq, mk_embedding]
/-
**NumberField.InfinitePlace.IsRamified.comap_embedding** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.InfinitePlace.IsRamified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K},   NumberField.InfinitePlac
e.IsRamified k w → (w.comap (algebraMap k K)).embedding = w.embedding.comp (alge
braMap k K)
参数：w.comap (algebraMap k K)；algebraMap k K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.comap_embedding_of_isReal`：comap_embedding_of_
isReal (f : k ->+* K) {w : InfinitePlace K} (h : (w.comap f).IsReal) : (w.comap 
f).embedding = w.embedding.comp f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isRamified_iff`：isRamified_iff : w.IsRamified 
k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
-/
lemma IsRamified.comap_embedding {w : InfinitePlace K} (h : w.IsRamified k) :
    (w.comap (algebraMap k K)).embedding = w.embedding.comp (algebraMap k K) := by
  rw [← comap_embedding_of_isReal _ (isRamified_iff.1 h).2]
/-
**NumberField.InfinitePlace.IsRamified.comap_embedding_conjugate** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.InfinitePlace.IsRamified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K},   NumberField.InfinitePlac
e.IsRamified k w →     (w.comap (algebraMap k K)).embedding = (NumberField.Compl
exEmbedding.conjugate w.embedding).comp (algebraMap k K)
参数：w.comap (algebraMap k K)；NumberField.ComplexEmbedding.conjugate w.embedding；a
lgebraMap k K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.ComplexEmbedding.isReal_iff`：isReal_iff {φ : K ->+* Complex}
 : IsReal φ ↔ conjugate φ = φ
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NumberField.InfinitePlace.isRamified_iff`：isRamified_iff : w.IsRamified 
k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.InfinitePlace.comap_embedding_of_isReal`：comap_embedding_of_
isReal (f : k ->+* K) {w : InfinitePlace K} (h : (w.comap f).IsReal) : (w.comap 
f).embedding = w.embedding.comp f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsRamified.comap_embedding_conjugate {w : InfinitePlace K} (h : w.IsRamified k) :
    (w.comap (algebraMap k K)).embedding = (conjugate w.embedding).comp (algebraMap k K) := by
  rw [← ComplexEmbedding.isReal_iff.1 <| isReal_iff.1 ((isRamified_iff.1 h).2)]
  simp [conjugate_comp, comap_embedding_of_isReal _ ((isRamified_iff.1 h).2)]
/-
**NumberField.InfinitePlace.IsRamified.isMixed_embedding** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace.IsRamified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K},   NumberField.InfinitePlac
e.IsRamified k w → NumberField.ComplexEmbedding.IsMixed k w.embedding
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.InfinitePlace.IsRamified.isReal`：∀ {k : Type u_1} [inst : Fi
eld k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : NumberFie
ld.InfinitePlace K}, NumberField.…
· 使用定理 `NumberField.InfinitePlace.comap_embedding_of_isReal`：comap_embedding_of_
isReal (f : k ->+* K) {w : InfinitePlace K} (h : (w.comap f).IsReal) : (w.comap 
f).embedding = w.embedding.comp f
· 使用定理 `NumberField.InfinitePlace.isComplex_iff`：isComplex_iff {w : InfinitePlac
e K} : IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.InfinitePlace.IsRamified.isComplex`：∀ {k : Type u_1} [inst :
 Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : Number
Field.InfinitePlace K}, NumberField.…
-/
lemma IsRamified.isMixed_embedding {w : InfinitePlace K} (h : w.IsRamified k) :
    IsMixed k w.embedding :=
  ⟨comap_embedding_of_isReal _ h.isReal ▸ isReal_iff.1 h.isReal, isComplex_iff.1 h.isComplex⟩
/-
**NumberField.InfinitePlace.IsRamified.isMixed_conjugate_embedding** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.InfinitePlace.IsRamified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K},   NumberField.InfinitePlac
e.IsRamified k w →     NumberField.ComplexEmbedding.IsMixed k (NumberField.Compl
exEmbedding.conjugate w.embedding)
参数：NumberField.ComplexEmbedding.conjugate w.embedding。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.InfinitePlace.IsRamified.isReal`：∀ {k : Type u_1} [inst : Fi
eld k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : NumberFie
ld.InfinitePlace K}, NumberField.…
· 使用定理 `NumberField.InfinitePlace.IsRamified.comap_embedding_conjugate`：∀ {k : T
ype u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k 
K]   {w : NumberField.InfinitePlace K},   NumberFiel…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.isComplex_iff`：isComplex_iff {w : InfinitePlac
e K} : IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.InfinitePlace.IsRamified.isComplex`：∀ {k : Type u_1} [inst :
 Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : Number
Field.InfinitePlace K}, NumberField.…
-/
lemma IsRamified.isMixed_conjugate_embedding {w : InfinitePlace K} (h : w.IsRamified k) :
    IsMixed k (conjugate w.embedding) :=
  ⟨h.comap_embedding_conjugate ▸ isReal_iff.1 h.isReal,
    by simpa using isComplex_iff.1 <| h.isComplex⟩
/-
**NumberField.InfinitePlace.isRamified_mk_iff_isMixed** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
形式化陈述：isRamified_mk_iff_isMixed {φ : K ->+* Complex} : (mk φ).IsRamified k ↔ IsM
ixed k φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq`：embedding_mk_eq (φ : K ->+* C
omplex) : embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ
· 使用定理 `NumberField.InfinitePlace.IsRamified.isMixed_embedding`：∀ {k : Type u_1}
 [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w 
: NumberField.InfinitePlace K},   NumberFiel…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `NumberField.InfinitePlace.IsRamified.isMixed_conjugate_embedding`：∀ {k :
 Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra 
k K]   {w : NumberField.InfinitePlace K},   NumberFiel…
· 使用定理 `NumberField.InfinitePlace.isRamified_iff`：isRamified_iff : w.IsRamified 
k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
· 使用定理 `NumberField.InfinitePlace.isComplex_iff`：isComplex_iff {w : InfinitePlac
e K} : IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w)
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq_of_isReal`：embedding_mk_eq_of_
isReal {φ : K ->+* Complex} (h : ComplexEmbedding.IsReal φ) : embedding (mk φ) =
 φ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem isRamified_mk_iff_isMixed {φ : K →+* ℂ} :
    (mk φ).IsRamified k ↔ IsMixed k φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases embedding_mk_eq φ with (hl | hr)
    · exact hl ▸ h.isMixed_embedding
    · rw [← star_star φ]; simpa [← congrArg conjugate hr] using h.isMixed_conjugate_embedding
  · rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, embedding_mk_eq_of_isReal h.1]
    exact ⟨by rcases embedding_mk_eq φ with (_ | _) <;> aesop, h.1⟩

alias ⟨_, _root_.NumberField.ComplexEmbedding.IsMixed.mk_isRamified⟩ := isRamified_mk_iff_isMixed
/-
**NumberField.InfinitePlace.IsUnramified.isUnmixed** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.InfinitePlace.IsUnramified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K},   NumberField.InfinitePlac
e.IsUnramified k w → NumberField.ComplexEmbedding.IsUnmixed k w.embedding
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff`：isUnramified_iff : IsUnramif
ied k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isComplex_iff_isReal`：not_isComplex_iff_is
Real {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
-/
lemma IsUnramified.isUnmixed {w : InfinitePlace K} (h : w.IsUnramified k) :
    IsUnmixed k w.embedding := by
  intro hw
  rw [← isReal_mk_iff, ← comap_mk, mk_embedding] at hw
  exact isReal_iff.1 <| (isUnramified_iff.1 h).resolve_right (not_isComplex_iff_isReal.2 hw)
/-
**NumberField.InfinitePlace.IsUnramified.isUnmixed_conjugate** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.InfinitePlace.IsUnramified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K},   NumberField.InfinitePlac
e.IsUnramified k w →     NumberField.ComplexEmbedding.IsUnmixed k (NumberField.C
omplexEmbedding.conjugate w.embedding)
参数：NumberField.ComplexEmbedding.conjugate w.embedding。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff`：isUnramified_iff : IsUnramif
ied k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isComplex_iff_isReal`：not_isComplex_iff_is
Real {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
-/
lemma IsUnramified.isUnmixed_conjugate {w : InfinitePlace K} (h : w.IsUnramified k) :
    IsUnmixed k (conjugate w.embedding) := by
  intro hw
  simp_rw [conjugate_comp, IsSelfAdjoint.star_iff, ← isReal_mk_iff, ← comap_mk, mk_embedding] at hw
  simpa using isReal_iff.1 <| (isUnramified_iff.1 h).resolve_right (not_isComplex_iff_isReal.2 hw)
/-
**NumberField.InfinitePlace.isUnramified_mk_iff_isUnmixed** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.InfinitePlace`。
形式化陈述：isUnramified_mk_iff_isUnmixed {φ : K ->+* Complex} : (mk φ).IsUnramified k
 ↔ IsUnmixed k φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq`：embedding_mk_eq (φ : K ->+* C
omplex) : embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ
· 使用定理 `NumberField.InfinitePlace.IsUnramified.isUnmixed`：∀ {k : Type u_1} [inst
 : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : Numb
erField.InfinitePlace K},   NumberFiel…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `NumberField.InfinitePlace.IsUnramified.isUnmixed_conjugate`：∀ {k : Type 
u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]  
 {w : NumberField.InfinitePlace K},   NumberFiel…
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff`：isUnramified_iff : IsUnramif
ied k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K))
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq_of_isReal`：embedding_mk_eq_of_
isReal {φ : K ->+* Complex} (h : ComplexEmbedding.IsReal φ) : embedding (mk φ) =
 φ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
-/
theorem isUnramified_mk_iff_isUnmixed {φ : K →+* ℂ} :
    (mk φ).IsUnramified k ↔ IsUnmixed k φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases embedding_mk_eq φ with (hl | hr)
    · exact hl ▸ h.isUnmixed
    · rw [← star_star φ]; simpa [← congrArg conjugate hr] using h.isUnmixed_conjugate
  · rw [isUnramified_iff, isReal_iff]
    by_cases hv : ComplexEmbedding.IsReal (φ.comp (algebraMap k K))
    · exact .inl <| by simp [embedding_mk_eq_of_isReal, h hv]
    · exact .inr <| by simpa using (isReal_mk_iff.not.2 hv)

alias ⟨_, _root_.NumberField.ComplexEmbedding.IsUnmixed.mk_isUnramified⟩ :=
  isUnramified_mk_iff_isUnmixed

variable (k)
/-
**NumberField.InfinitePlace.IsReal.isUnramified** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.InfinitePlace.IsReal`。
形式化陈述：∀ (k : Type u_1) [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K}, w.IsReal → NumberField.Inf
initePlace.IsUnramified k w
参数：k : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff`：isUnramified_iff : IsUnramif
ied k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K))
-/
lemma IsReal.isUnramified (h : IsReal w) : IsUnramified k w := isUnramified_iff.mpr (Or.inl h)

variable {k}
/-
**NumberField.InfinitePlace._root_.NumberField.ComplexEmbedding.IsConj.isUnramif
ied_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff
    {φ : K →+* ℂ} (h : ComplexEmbedding.IsConj φ σ) :
    IsUnramified k (mk φ) ↔ σ = 1 := by
  rw [h.ext_iff, ComplexEmbedding.isConj_one_iff, ← not_iff_not, not_isUnramified_iff,
    ← not_isReal_iff_isComplex, comap_mk, isReal_mk_iff, isReal_mk_iff, eq_true h.isReal_comp,
    and_true]
/-
**NumberField.InfinitePlace.isUnramified_mk_iff_forall_isConj** 是 Mathlib 中的一个引理
，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：isUnramified_mk_iff_forall_isConj [IsGalois k K] {φ : K ->+* Complex} : Is
Unramified k (mk φ) ↔ forall σ : Gal(K/k), ComplexEmbedding.IsConj φ σ -> σ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff`：∀ {k : Type u_1
} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K] {σ :
 Gal(K/k)} {φ : K →+* ℂ},   NumberField.Compl…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NumberField.ComplexEmbedding.isConj_one_iff`：isConj_one_iff : IsConj φ (
1 : Gal(K/k)) ↔ IsReal φ
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用引理 `NumberField.InfinitePlace.not_isUnramified_iff`：not_isUnramified_iff : ¬
 IsUnramified k w ↔ IsComplex w ∧ IsReal (w.comap (algebraMap k K))
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHom.restrictNormal_commutes`：AlgHom.restrictNormal_commutes [Normal F
 E] (x : E) : algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma isUnramified_mk_iff_forall_isConj [IsGalois k K] {φ : K →+* ℂ} :
    IsUnramified k (mk φ) ↔ ∀ σ : Gal(K/k), ComplexEmbedding.IsConj φ σ → σ = 1 := by
  refine ⟨fun H σ hσ ↦ hσ.isUnramified_mk_iff.mp H,
    fun H ↦ ?_⟩
  by_contra hφ
  rw [not_isUnramified_iff] at hφ
  rw [comap_mk, isReal_mk_iff, ← not_isReal_iff_isComplex, isReal_mk_iff,
    ← ComplexEmbedding.isConj_one_iff (k := k)] at hφ
  let := (φ.comp (algebraMap k K)).toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let φ' : K →ₐ[k] ℂ := { star φ with
    commutes' := fun r ↦ by simpa using! RingHom.congr_fun hφ.2 r }
  have : ComplexEmbedding.IsConj φ (AlgHom.restrictNormal' φ' K) :=
    (RingHom.ext <| AlgHom.restrictNormal_commutes φ' K).symm
  exact hφ.1 (H _ this ▸ this)

local notation "Stab" => MulAction.stabilizer Gal(K/k)
/-
**NumberField.InfinitePlace.mem_stabilizer_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `Num
berField.InfinitePlace`。
形式化陈述：mem_stabilizer_mk_iff (φ : K ->+* Complex) (σ : Gal(K/k)) : σ in Stab (mk 
φ) ↔ σ = 1 ∨ ComplexEmbedding.IsConj φ σ
参数：φ : K ->+* Complex；σ : Gal(K/k)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NumberField.ComplexEmbedding.isConj_symm`：isConj_symm : IsConj φ σ.symm 
↔ IsConj φ σ
· 使用定理 `NumberField.ComplexEmbedding.conjugate.eq_1`：∀ {K : Type u_1} [inst : Fi
eld K] (φ : K →+* ℂ), NumberField.ComplexEmbedding.conjugate φ = star φ
· 使用定理 `star_eq_iff_star_eq`：star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : 
star r = s ↔ star s = r
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_stabilizer_mk_iff (φ : K →+* ℂ) (σ : Gal(K/k)) :
    σ ∈ Stab (mk φ) ↔ σ = 1 ∨ ComplexEmbedding.IsConj φ σ := by
  simp only [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_iff]
  rw [← ComplexEmbedding.isConj_symm, ComplexEmbedding.conjugate, star_eq_iff_star_eq]
  refine or_congr ⟨fun H ↦ ?_, fun H ↦ H ▸ rfl⟩ Iff.rfl
  exact congr_arg AlgEquiv.symm
    (AlgEquiv.ext (g := AlgEquiv.refl) fun x ↦ φ.injective (RingHom.congr_fun H x))
/-
**NumberField.InfinitePlace.IsUnramified.stabilizer_eq_bot** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.InfinitePlace.IsUnramified`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_
2 : Algebra k K]   {w : NumberField.InfinitePlace K}, NumberField.InfinitePlace.
IsUnramified k w → MulAction.stabilizer Gal(K/k) w = ⊥
参数：K/k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff`：∀ {k : Type u_1
} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K] {σ :
 Gal(K/k)} {φ : K →+* ℂ},   NumberField.Compl…
-/
lemma IsUnramified.stabilizer_eq_bot (h : IsUnramified k w) : Stab w = ⊥ := by
  rw [eq_bot_iff, ← mk_embedding w, SetLike.le_def]
  simp only [mem_stabilizer_mk_iff, Subgroup.mem_bot, forall_eq_or_imp, true_and]
  exact fun σ hσ ↦ hσ.isUnramified_mk_iff.mp ((mk_embedding w).symm ▸ h)
/-
**NumberField.InfinitePlace._root_.NumberField.ComplexEmbedding.IsConj.coe_stabi
lizer_mk** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NumberField.ComplexEmbedding.IsConj.coe_stabilizer_mk
    {φ : K →+* ℂ} (h : ComplexEmbedding.IsConj φ σ) :
    (Stab (mk φ) : Set Gal(K/k)) = {1, σ} := by
  ext
  rw [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    ← h.ext_iff, eq_comm (a := σ)]

variable (k w)
/-
**NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two** 是 Mathlib 中的一个引理
，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：nat_card_stabilizer_eq_one_or_two : Nat.card (Stab w) = 1 ∨ Nat.card (Stab
 w) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_sort_coe`：coe_sort_coe : ((p : Set B) : Type _) = p
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `NumberField.ComplexEmbedding.IsConj.coe_stabilizer_mk`：∀ {k : Type u_1} 
[inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K] {σ : G
al(K/k)} {φ : K →+* ℂ},   NumberField.Compl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Set.toFinset_singleton`：toFinset_singleton (a : α) [Fintype ({a} : Set α
)] : ({a} : Set α).toFinset = {a}
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nat_card_stabilizer_eq_one_or_two :
    Nat.card (Stab w) = 1 ∨ Nat.card (Stab w) = 2 := by
  classical
  rw [← SetLike.coe_sort_coe, ← mk_embedding w]
  by_cases! h : ∃ σ, ComplexEmbedding.IsConj (k := k) (embedding w) σ
  · obtain ⟨σ, hσ⟩ := h
    rw [hσ.coe_stabilizer_mk]
    simp
  · left
    trans Nat.card ({1} : Set Gal(K/k))
    · congr with x
      simp only [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_singleton_iff, or_iff_left_iff_imp,
        h x, IsEmpty.forall_iff]
    · simp

variable {k w}
/-
**NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot** 是 Mathlib 中的一个引
理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：isUnramified_iff_stabilizer_eq_bot [IsGalois k K] : IsUnramified k w ↔ Sta
b w = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用引理 `NumberField.InfinitePlace.isUnramified_mk_iff_forall_isConj`：isUnramifie
d_mk_iff_forall_isConj [IsGalois k K] {φ : K ->+* Complex} : IsUnramified k (mk 
φ) ↔ forall σ : Gal(K/k), ComplexEmbedding.IsConj…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isUnramified_iff_stabilizer_eq_bot [IsGalois k K] : IsUnramified k w ↔ Stab w = ⊥ := by
  rw [← mk_embedding w, isUnramified_mk_iff_forall_isConj]
  simp only [eq_bot_iff, SetLike.le_def, mem_stabilizer_mk_iff,
    Subgroup.mem_bot, forall_eq_or_imp, true_and]
/-
**NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one** 是 Mathlib 
中的一个引理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：isUnramified_iff_card_stabilizer_eq_one [IsGalois k K] : IsUnramified k w 
↔ Nat.card (Stab w) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot`：isUnramifi
ed_iff_stabilizer_eq_bot [IsGalois k K] : IsUnramified k w ↔ Stab w = ⊥
· 使用定理 `Subgroup.card_eq_one`：card_eq_one : Nat.card H = 1 ↔ H = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isUnramified_iff_card_stabilizer_eq_one [IsGalois k K] :
    IsUnramified k w ↔ Nat.card (Stab w) = 1 := by
  rw [isUnramified_iff_stabilizer_eq_bot, Subgroup.card_eq_one]
/-
**NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two** 是 Math
lib 中的一个引理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：not_isUnramified_iff_card_stabilizer_eq_two [IsGalois k K] : ¬ IsUnramifie
d k w ↔ Nat.card (Stab w) = 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one`：isUnr
amified_iff_card_stabilizer_eq_one [IsGalois k K] : IsUnramified k w ↔ Nat.card 
(Stab w) = 1
· 使用引理 `NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two`：nat_card_st
abilizer_eq_one_or_two : Nat.card (Stab w) = 1 ∨ Nat.card (Stab w) = 2
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma not_isUnramified_iff_card_stabilizer_eq_two [IsGalois k K] :
    ¬ IsUnramified k w ↔ Nat.card (Stab w) = 2 := by
  rw [isUnramified_iff_card_stabilizer_eq_one]
  obtain (e | e) := nat_card_stabilizer_eq_one_or_two k w <;> rw [e] <;> decide
/-
**NumberField.InfinitePlace.isRamified_iff_card_stabilizer_eq_two** 是 Mathlib 中的
一个引理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：isRamified_iff_card_stabilizer_eq_two [IsGalois k K] : IsRamified k w ↔ Na
t.card (Stab w) = 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two`：n
ot_isUnramified_iff_card_stabilizer_eq_two [IsGalois k K] : ¬ IsUnramified k w ↔
 Nat.card (Stab w) = 2
-/
lemma isRamified_iff_card_stabilizer_eq_two [IsGalois k K] :
    IsRamified k w ↔ Nat.card (Stab w) = 2 :=
  not_isUnramified_iff_card_stabilizer_eq_two
/-
**NumberField.InfinitePlace.exists_isConj_of_isRamified** 是 Mathlib 中的一个引理，位于命名空
间 `NumberField.InfinitePlace`。
形式化陈述：exists_isConj_of_isRamified [IsGalois k K] {φ : K ->+* Complex} (h : IsRam
ified k (mk φ)) : exists σ : Gal(K/k), ComplexEmbedding.IsConj φ σ
参数：h : IsRamified k (mk φ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_two_iff`：card_eq_two_iff : Nat.card α = 2 ↔ exists x y : α, 
x != y ∧ {x, y} = @Set.univ α
· 使用引理 `NumberField.InfinitePlace.isRamified_iff_card_stabilizer_eq_two`：isRamif
ied_iff_card_stabilizer_eq_two [IsGalois k K] : IsRamified k w ↔ Nat.card (Stab 
w) = 2
· 使用引理 `NumberField.InfinitePlace.mem_stabilizer_mk_iff`：mem_stabilizer_mk_iff (
φ : K ->+* Complex) (σ : Gal(K/k)) : σ in Stab (mk φ) ↔ σ = 1 ∨ ComplexEmbedding
.IsConj φ σ
-/
lemma exists_isConj_of_isRamified [IsGalois k K] {φ : K →+* ℂ} (h : IsRamified k (mk φ)) :
    ∃ σ : Gal(K/k), ComplexEmbedding.IsConj φ σ := by
  rw [isRamified_iff_card_stabilizer_eq_two, Nat.card_eq_two_iff] at h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, h₁, -⟩ := h
  rw [mem_stabilizer_mk_iff] at hx hy
  grind

open scoped Classical in
/-
**NumberField.InfinitePlace.card_stabilizer** 是 Mathlib 中的一个引理，位于命名空间 `NumberFie
ld.InfinitePlace`。
形式化陈述：card_stabilizer [IsGalois k K] : Nat.card (Stab w) = if IsUnramified k w t
hen 1 else 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two`：n
ot_isUnramified_iff_card_stabilizer_eq_two [IsGalois k K] : ¬ IsUnramified k w ↔
 Nat.card (Stab w) = 2
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one`：isUnr
amified_iff_card_stabilizer_eq_one [IsGalois k K] : IsUnramified k w ↔ Nat.card 
(Stab w) = 1
-/
lemma card_stabilizer [IsGalois k K] :
    Nat.card (Stab w) = if IsUnramified k w then 1 else 2 := by
  split
  · rwa [← isUnramified_iff_card_stabilizer_eq_one]
  · rwa [← not_isUnramified_iff_card_stabilizer_eq_two]
/-
**NumberField.InfinitePlace.even_nat_card_aut_of_not_isUnramified** 是 Mathlib 中的
一个引理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：even_nat_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified 
k w) : Even (Nat.card Gal(K/k))
参数：hw : ¬ IsUnramified k w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two`：n
ot_isUnramified_iff_card_stabilizer_eq_two [IsGalois k K] : ¬ IsUnramified k w ↔
 Nat.card (Stab w) = 2
· 使用定理 `Subgroup.card_subgroup_dvd_card`：card_subgroup_dvd_card (s : Subgroup α)
 : Nat.card s ∣ Nat.card α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用引理 `Even.zero`：Even.zero [Zero β] : Function.Even (fun (_ : α) => (0 : β))
-/
lemma even_nat_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) :
    Even (Nat.card Gal(K/k)) := by
  by_cases H : Finite Gal(K/k)
  · cases nonempty_fintype Gal(K/k)
    rw [even_iff_two_dvd, ← not_isUnramified_iff_card_stabilizer_eq_two.mp hw]
    exact Subgroup.card_subgroup_dvd_card (Stab w)
  · convert! Even.zero
    by_contra e
    exact H (Nat.finite_of_card_ne_zero e)
/-
**NumberField.InfinitePlace.even_card_aut_of_not_isUnramified** 是 Mathlib 中的一个引理
，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：even_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w)
 : Even (Nat.card Gal(K/k))
参数：hw : ¬ IsUnramified k w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.even_nat_card_aut_of_not_isUnramified`：even_na
t_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) : Even (
Nat.card Gal(K/k))
-/
lemma even_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) :
    Even (Nat.card Gal(K/k)) :=
  even_nat_card_aut_of_not_isUnramified hw
/-
**NumberField.InfinitePlace.even_finrank_of_not_isUnramified** 是 Mathlib 中的一个引理，
位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：even_finrank_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) 
: Even (finrank k K)
参数：hw : ¬ IsUnramified k w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.even_card_aut_of_not_isUnramified`：even_card_a
ut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) : Even (Nat.card
 Gal(K/k))
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用引理 `Even.zero`：Even.zero [Zero β] : Function.Even (fun (_ : α) => (0 : β))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_of_not_finite`：finrank_of_not_finite (h : ¬Module.Finite 
R M) : finrank R M = 0
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
lemma even_finrank_of_not_isUnramified [IsGalois k K]
    (hw : ¬ IsUnramified k w) : Even (finrank k K) := by
  by_cases FiniteDimensional k K
  · exact IsGalois.card_aut_eq_finrank k K ▸ even_card_aut_of_not_isUnramified hw
  · exact finrank_of_not_finite ‹_› ▸ Even.zero
/-
**NumberField.InfinitePlace.isUnramified_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Num
berField.InfinitePlace`。
形式化陈述：isUnramified_smul_iff : IsUnramified k (σ • w) ↔ IsUnramified k w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff`：isUnramified_iff : IsUnramif
ied k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K))
· 使用引理 `NumberField.InfinitePlace.isReal_smul_iff`：isReal_smul_iff : IsReal (σ •
 w) ↔ IsReal w
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `NumberField.InfinitePlace.comap_smul`：comap_smul {f : F ->+* K} : (σ • w
).comap f = w.comap (RingHom.comp σ.symm f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgEquiv.toAlgHom_toRingHom`：toAlgHom_toRingHom : ((e : A₁ ->ₐ[R] A₂) : 
A₁ ->+* A₂) = e
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isUnramified_smul_iff :
    IsUnramified k (σ • w) ↔ IsUnramified k w := by
  rw [isUnramified_iff, isUnramified_iff, isReal_smul_iff, comap_smul,
    ← AlgEquiv.toAlgHom_toRingHom, AlgHom.comp_algebraMap]

variable (K) in
/-- An infinite place of the base field is unramified in a field extension if every
infinite place over it is unramified. -/
/-
**NumberField.InfinitePlace.IsUnramifiedIn** 是 Mathlib 中的一个定义，位于命名空间 `NumberFiel
d.InfinitePlace`。
形式化陈述：IsUnramifiedIn (w : InfinitePlace k) : Prop
参数：w : InfinitePlace k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite place of the base field is unramified in a field extension if every
infinite place over it is unramified.
-/
def IsUnramifiedIn (w : InfinitePlace k) : Prop :=
  ∀ v, comap v (algebraMap k K) = w → IsUnramified k v
/-
**NumberField.InfinitePlace.isUnramifiedIn_comap** 是 Mathlib 中的一个引理，位于命名空间 `Numb
erField.InfinitePlace`。
形式化陈述：isUnramifiedIn_comap [IsGalois k K] {w : InfinitePlace K} : (w.comap (alge
braMap k K)).IsUnramifiedIn K ↔ w.IsUnramified k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.exists_smul_eq_of_comap_eq`：exists_smul_eq_of_
comap_eq [IsGalois k K] {w w' : InfinitePlace K} (h : w.comap (algebraMap k K) =
 w'.comap (algebraMap k K)) : exists σ : G…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.isUnramified_smul_iff`：isUnramified_smul_iff :
 IsUnramified k (σ • w) ↔ IsUnramified k w
-/
lemma isUnramifiedIn_comap [IsGalois k K] {w : InfinitePlace K} :
    (w.comap (algebraMap k K)).IsUnramifiedIn K ↔ w.IsUnramified k := by
  refine ⟨fun H ↦ H _ rfl, fun H v hv ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_comap_eq hv
  rwa [isUnramified_smul_iff] at H
/-
**NumberField.InfinitePlace.even_card_aut_of_not_isUnramifiedIn** 是 Mathlib 中的一个
引理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：even_card_aut_of_not_isUnramifiedIn [IsGalois k K] {w : InfinitePlace k} (
hw : ¬ w.IsUnramifiedIn K) : Even (Nat.card Gal(K/k))
参数：hw : ¬ w.IsUnramifiedIn K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.comap_surjective`：comap_surjective [Algebra k 
K] [Algebra.IsAlgebraic k K] : Function.Surjective (comap · (algebraMap k K))
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用引理 `NumberField.InfinitePlace.even_card_aut_of_not_isUnramified`：even_card_a
ut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) : Even (Nat.card
 Gal(K/k))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.isUnramifiedIn_comap`：isUnramifiedIn_comap [Is
Galois k K] {w : InfinitePlace K} : (w.comap (algebraMap k K)).IsUnramifiedIn K 
↔ w.IsUnramified k
-/
lemma even_card_aut_of_not_isUnramifiedIn [IsGalois k K]
    {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (Nat.card Gal(K/k)) := by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_card_aut_of_not_isUnramified hw
/-
**NumberField.InfinitePlace.even_finrank_of_not_isUnramifiedIn** 是 Mathlib 中的一个引
理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：even_finrank_of_not_isUnramifiedIn [IsGalois k K] {w : InfinitePlace k} (h
w : ¬ w.IsUnramifiedIn K) : Even (finrank k K)
参数：hw : ¬ w.IsUnramifiedIn K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.comap_surjective`：comap_surjective [Algebra k 
K] [Algebra.IsAlgebraic k K] : Function.Surjective (comap · (algebraMap k K))
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用引理 `NumberField.InfinitePlace.even_finrank_of_not_isUnramified`：even_finrank
_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) : Even (finrank k 
K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.isUnramifiedIn_comap`：isUnramifiedIn_comap [Is
Galois k K] {w : InfinitePlace K} : (w.comap (algebraMap k K)).IsUnramifiedIn K 
↔ w.IsUnramified k
-/
lemma even_finrank_of_not_isUnramifiedIn
    [IsGalois k K] {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (finrank k K) := by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_finrank_of_not_isUnramified hw

variable (k K)
variable [NumberField K]

open Finset in
open scoped Classical in
/-
**NumberField.InfinitePlace.card_isUnramified** 是 Mathlib 中的一个引理，位于命名空间 `NumberF
ield.InfinitePlace`。
形式化陈述：card_isUnramified [NumberField k] [IsGalois k K] : #{w : InfinitePlace K |
 w.IsUnramified k} = #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `NumberField.instFiniteDimensional`：∀ (K : Type u_1) (L : Type u_2) [inst
 : Field K] [inst_1 : Field L] [NumberField K] [NumberField L]   [inst_4 : Algeb
ra K L], FiniteDimensio…
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `NumberField.InfinitePlace.comap_surjective`：comap_surjective [Algebra k 
K] [Algebra.IsAlgebraic k K] : Function.Surjective (comap · (algebraMap k K))
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_filter_univ`：mem_filter_univ {p : α -> Prop} [DecidablePred p
] : forall x, x in univ.filter p ↔ p x
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用引理 `NumberField.InfinitePlace.mem_orbit_iff`：mem_orbit_iff [IsGalois k K] {w
 w' : InfinitePlace K} : w' in MulAction.orbit Gal(K/k) w ↔ w.comap (algebraMap 
k K) = w'.comap (algebraMap k…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用引理 `NumberField.InfinitePlace.isUnramifiedIn_comap`：isUnramifiedIn_comap [Is
Galois k K] {w : InfinitePlace K} : (w.comap (algebraMap k K)).IsUnramifiedIn K 
↔ w.IsUnramified k
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`：card_orbit_mul_c
ard_stabilizer_eq_card_group (b : X) [Fintype G] [Fintype <| orbit G b] [Fintype
 <| stabilizer G b] : Fintype.card (orbit G …
（共 34 条，此处仅展示前 30 条）
-/
lemma card_isUnramified [NumberField k] [IsGalois k K] :
    #{w : InfinitePlace K | w.IsUnramified k} =
      #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K := by
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := {w : InfinitePlace k | w.IsUnramifiedIn K}), ← smul_eq_mul, ← sum_const]
  · refine sum_congr rfl (fun w hw ↦ ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    rw [mem_filter_univ] at hw
    trans #(MulAction.orbit Gal(K/k) w).toFinset
    · congr; ext w'
      rw [mem_filter, mem_filter_univ, Set.mem_toFinset, mem_orbit_iff, @eq_comm _ (comap w' _),
        and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [Nat.card_eq_fintype_card,
        ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), card_stabilizer, if_pos,
        mul_one, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

open Finset in
open scoped Classical in
/-
**NumberField.InfinitePlace.card_isUnramified_compl** 是 Mathlib 中的一个引理，位于命名空间 `N
umberField.InfinitePlace`。
形式化陈述：card_isUnramified_compl [NumberField k] [IsGalois k K] : #({w : InfinitePl
ace K | w.IsUnramified k} : Finset _)ᶜ = #({w : InfinitePlace k | w.IsUnramified
In K} : Finset _)ᶜ * (finrank k K / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `NumberField.instFiniteDimensional`：∀ (K : Type u_1) (L : Type u_2) [inst
 : Field K] [inst_1 : Field L] [NumberField K] [NumberField L]   [inst_4 : Algeb
ra K L], FiniteDimensio…
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.compl_filter`：compl_filter (p : α -> Prop) [DecidablePred p] [for
all x, Decidable ¬p x] : (univ.filter p)ᶜ = univ.filter fun x => ¬p x
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `NumberField.InfinitePlace.comap_surjective`：comap_surjective [Algebra k 
K] [Algebra.IsAlgebraic k K] : Function.Surjective (comap · (algebraMap k K))
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_filter_univ`：mem_filter_univ {p : α -> Prop} [DecidablePred p
] : forall x, x in univ.filter p ↔ p x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用引理 `NumberField.InfinitePlace.mem_orbit_iff`：mem_orbit_iff [IsGalois k K] {w
 w' : InfinitePlace K} : w' in MulAction.orbit Gal(K/k) w ↔ w.comap (algebraMap 
k K) = w'.comap (algebraMap k…
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用引理 `NumberField.InfinitePlace.isUnramifiedIn_comap`：isUnramifiedIn_comap [Is
Galois k K] {w : InfinitePlace K} : (w.comap (algebraMap k K)).IsUnramifiedIn K 
↔ w.IsUnramified k
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
（共 39 条，此处仅展示前 30 条）
-/
lemma card_isUnramified_compl [NumberField k] [IsGalois k K] :
    #({w : InfinitePlace K | w.IsUnramified k} : Finset _)ᶜ =
      #({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2) := by
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := ({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ), ← smul_eq_mul, ← sum_const]
  · refine sum_congr rfl (fun w hw ↦ ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    rw [compl_filter, mem_filter_univ] at hw
    trans Finset.card (MulAction.orbit Gal(K/k) w).toFinset
    · congr; ext w'
      rw [mem_filter, compl_filter, mem_filter_univ, @eq_comm _ (comap w' _), Set.mem_toFinset,
        mem_orbit_iff, and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [Nat.card_eq_fintype_card,
        ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), InfinitePlace.card_stabilizer, if_neg,
        Nat.mul_div_cancel _ zero_lt_two, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

open scoped Classical in
/-
**NumberField.InfinitePlace.card_eq_card_isUnramifiedIn** 是 Mathlib 中的一个引理，位于命名空
间 `NumberField.InfinitePlace`。
形式化陈述：card_eq_card_isUnramifiedIn [NumberField k] [IsGalois k K] : Fintype.card 
(InfinitePlace K) = #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K + 
#({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NumberField.InfinitePlace.card_isUnramified`：card_isUnramified [NumberFi
eld k] [IsGalois k K] : #{w : InfinitePlace K | w.IsUnramified k} = #{w : Infini
tePlace k | w.IsUnramifiedIn K} *…
· 使用引理 `NumberField.InfinitePlace.card_isUnramified_compl`：card_isUnramified_com
pl [NumberField k] [IsGalois k K] : #({w : InfinitePlace K | w.IsUnramified k} :
 Finset _)ᶜ = #({w : InfinitePlace k | …
· 使用定理 `Finset.card_add_card_compl`：Finset.card_add_card_compl [DecidableEq α] [
Fintype α] (s : Finset α) : #s + #sᶜ = Fintype.card α
-/
lemma card_eq_card_isUnramifiedIn [NumberField k] [IsGalois k K] :
    Fintype.card (InfinitePlace K) =
      #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K +
      #({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2) := by
  rw [← card_isUnramified, ← card_isUnramified_compl, Finset.card_add_card_compl]

end NumberField.InfinitePlace

open NumberField

variable (k : Type*) [Field k] (K : Type*) [Field K] (F : Type*) [Field F]

variable [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]

/-- A field extension is unramified at infinite places if every infinite place is unramified. -/
/-
**IsUnramifiedAtInfinitePlaces** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u_1) → [inst : Field k] → (K : Type u_2) → [inst_1 : Field K] → 
[Algebra k K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field extension is unramified at infinite places if every infinite place is un
ramified.
-/
class IsUnramifiedAtInfinitePlaces : Prop where
  isUnramified : ∀ w : InfinitePlace K, w.IsUnramified k
/-
**IsUnramifiedAtInfinitePlaces.id** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUnramifiedAtInfinitePlaces.id : IsUnramifiedAtInfinitePlaces K K where i
sUnramified w
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.isUnramified_self`：isUnramified_self : IsUnram
ified K w
-/
instance IsUnramifiedAtInfinitePlaces.id : IsUnramifiedAtInfinitePlaces K K where
  isUnramified w := w.isUnramified_self
/-
**IsUnramifiedAtInfinitePlaces.trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnramifiedAtInfinitePlaces.trans [h₁ : IsUnramifiedAtInfinitePlaces k K]
 [h₂ : IsUnramifiedAtInfinitePlaces K F] : IsUnramifiedAtInfinitePlaces k F wher
e isUnramified w
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUnramifiedAtInfinitePlaces.isUnramified`：∀ {k : Type u_1} {inst : Fiel
d k} {K : Type u_2} {inst_1 : Field K} {inst_2 : Algebra k K}   [self : IsUnrami
fiedAtInfinitePlaces k K] (w : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
lemma IsUnramifiedAtInfinitePlaces.trans
    [h₁ : IsUnramifiedAtInfinitePlaces k K] [h₂ : IsUnramifiedAtInfinitePlaces K F] :
    IsUnramifiedAtInfinitePlaces k F where
  isUnramified w :=
    Eq.trans (IsScalarTower.algebraMap_eq k K F ▸ h₁.1 (w.comap (algebraMap _ _))) (h₂.1 w)
/-
**IsUnramifiedAtInfinitePlaces.top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnramifiedAtInfinitePlaces.top [h : IsUnramifiedAtInfinitePlaces k F] : 
IsUnramifiedAtInfinitePlaces K F where isUnramified w
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.IsUnramified.of_restrictScalars`：∀ {k : Type u
_1} [inst : Field k] (K : Type u_2) [inst_1 : Field K] {F : Type u_3} [inst_2 : 
Field F]   [inst_3 : Algebra k K] [inst_4 : Alg…
· 使用定理 `IsUnramifiedAtInfinitePlaces.isUnramified`：∀ {k : Type u_1} {inst : Fiel
d k} {K : Type u_2} {inst_1 : Field K} {inst_2 : Algebra k K}   [self : IsUnrami
fiedAtInfinitePlaces k K] (w : …
-/
lemma IsUnramifiedAtInfinitePlaces.top [h : IsUnramifiedAtInfinitePlaces k F] :
    IsUnramifiedAtInfinitePlaces K F where
  isUnramified w := (h.1 w).of_restrictScalars K
/-
**IsUnramifiedAtInfinitePlaces.bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnramifiedAtInfinitePlaces.bot [h₁ : IsUnramifiedAtInfinitePlaces k F] [
Algebra.IsAlgebraic K F] : IsUnramifiedAtInfinitePlaces k K where isUnramified w
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.comap_surjective`：comap_surjective [Algebra k 
K] [Algebra.IsAlgebraic k K] : Function.Surjective (comap · (algebraMap k K))
· 使用定理 `NumberField.InfinitePlace.IsUnramified.comap`：∀ {k : Type u_1} [inst : F
ield k] (K : Type u_2) [inst_1 : Field K] {F : Type u_3} [inst_2 : Field F]   [i
nst_3 : Algebra k K] [inst_4 : Alg…
· 使用定理 `IsUnramifiedAtInfinitePlaces.isUnramified`：∀ {k : Type u_1} {inst : Fiel
d k} {K : Type u_2} {inst_1 : Field K} {inst_2 : Algebra k K}   [self : IsUnrami
fiedAtInfinitePlaces k K] (w : …
-/
lemma IsUnramifiedAtInfinitePlaces.bot [h₁ : IsUnramifiedAtInfinitePlaces k F]
    [Algebra.IsAlgebraic K F] :
    IsUnramifiedAtInfinitePlaces k K where
  isUnramified w := by
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := F) w
    exact (h₁.1 w).comap K

variable {K}
/-
**NumberField.InfinitePlace.isUnramified** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NumberField.InfinitePlace.isUnramified [IsUnramifiedAtInfinitePlaces k K] 
(w : InfinitePlace K) : IsUnramified k w
参数：w : InfinitePlace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnramifiedAtInfinitePlaces.isUnramified`：∀ {k : Type u_1} {inst : Fiel
d k} {K : Type u_2} {inst_1 : Field K} {inst_2 : Algebra k K}   [self : IsUnrami
fiedAtInfinitePlaces k K] (w : …
-/
lemma NumberField.InfinitePlace.isUnramified [IsUnramifiedAtInfinitePlaces k K]
    (w : InfinitePlace K) : IsUnramified k w := IsUnramifiedAtInfinitePlaces.isUnramified w

variable {k} (K)
/-
**NumberField.InfinitePlace.isUnramifiedIn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NumberField.InfinitePlace.isUnramifiedIn [IsUnramifiedAtInfinitePlaces k K
] (w : InfinitePlace k) : IsUnramifiedIn K w
参数：w : InfinitePlace k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.isUnramified`：NumberField.InfinitePlace.isUnra
mified [IsUnramifiedAtInfinitePlaces k K] (w : InfinitePlace K) : IsUnramified k
 w
-/
lemma NumberField.InfinitePlace.isUnramifiedIn [IsUnramifiedAtInfinitePlaces k K]
    (w : InfinitePlace k) : IsUnramifiedIn K w := fun v _ ↦ v.isUnramified k

variable {K}
/-
**IsUnramifiedAtInfinitePlaces_of_odd_card_aut** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnramifiedAtInfinitePlaces_of_odd_card_aut [IsGalois k K] (h : Odd (Nat.
card Gal(K/k))) : IsUnramifiedAtInfinitePlaces k K
参数：h : Odd (Nat.card Gal(K/k))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用引理 `NumberField.InfinitePlace.even_card_aut_of_not_isUnramified`：even_card_a
ut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) : Even (Nat.card
 Gal(K/k))
-/
lemma IsUnramifiedAtInfinitePlaces_of_odd_card_aut [IsGalois k K]
    (h : Odd (Nat.card Gal(K/k))) : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ ↦ not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_card_aut_of_not_isUnramified)⟩
/-
**IsUnramifiedAtInfinitePlaces_of_odd_finrank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnramifiedAtInfinitePlaces_of_odd_finrank [IsGalois k K] (h : Odd (Modul
e.finrank k K)) : IsUnramifiedAtInfinitePlaces k K
参数：h : Odd (Module.finrank k K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用引理 `NumberField.InfinitePlace.even_finrank_of_not_isUnramified`：even_finrank
_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) : Even (finrank k 
K)
-/
lemma IsUnramifiedAtInfinitePlaces_of_odd_finrank [IsGalois k K]
    (h : Odd (Module.finrank k K)) : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ ↦ not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_finrank_of_not_isUnramified)⟩

variable (k K)

open Module in
/-
**IsUnramifiedAtInfinitePlaces.card_infinitePlace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnramifiedAtInfinitePlaces.card_infinitePlace [NumberField k] [NumberFie
ld K] [IsGalois k K] [IsUnramifiedAtInfinitePlaces k K] : Fintype.card (Infinite
Place K) = Fintype.card (InfinitePlace k) * finrank k K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.card_eq_card_isUnramifiedIn`：card_eq_card_isUn
ramifiedIn [NumberField k] [IsGalois k K] : Fintype.card (InfinitePlace K) = #{w
 : InfinitePlace k | w.IsUnramifiedIn K} * …
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `NumberField.InfinitePlace.isUnramifiedIn`：NumberField.InfinitePlace.isUn
ramifiedIn [IsUnramifiedAtInfinitePlaces k K] (w : InfinitePlace k) : IsUnramifi
edIn K w
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.compl_univ`：compl_univ : (univ : Finset α)ᶜ = ∅
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma IsUnramifiedAtInfinitePlaces.card_infinitePlace [NumberField k] [NumberField K]
    [IsGalois k K] [IsUnramifiedAtInfinitePlaces k K] :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace k) * finrank k K := by
  classical
  rw [InfinitePlace.card_eq_card_isUnramifiedIn (k := k) (K := K), Finset.filter_true_of_mem,
    Finset.card_univ, Finset.card_eq_zero.mpr, zero_mul, add_zero]
  · exact Finset.compl_univ
  simp only [Finset.mem_univ, forall_true_left]
  exact InfinitePlace.isUnramifiedIn K

namespace NumberField.InfinitePlace

open ComplexEmbedding AbsoluteValue

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

section LiesOver

variable (w : InfinitePlace L) (v : InfinitePlace K) [w.LiesOver v]

namespace LiesOver

/-
**NumberField.InfinitePlace.LiesOver.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Inf
initePlace.LiesOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {φ : K →+* ℂ} {ψ : L →+* ℂ} [ComplexEmbedding.LiesOver ψ φ] :
    AbsoluteValue.LiesOver (mk ψ).1 (mk φ).1 where
  comp_eq := by simp [← LiesOver.over ψ φ, ← coe_mk_comp]
/-
**NumberField.InfinitePlace.LiesOver.comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.InfinitePlace.LiesOver`。
形式化陈述：comap_eq : w.comap (algebraMap K L) = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.ext`：ext (v₁ v₂ : InfinitePlace K) (h : forall
 k, v₁ k = v₂ k) : v₁ = v₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `AbsoluteValue.ext_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {f g : AbsoluteValue R S}, 
f = g ↔ ∀ (…
· 使用定理 `AbsoluteValue.LiesOver.comp_eq`：∀ {K : Type u_3} {L : Type u_4} {S : Typ
e u_5} {inst : CommRing K} {inst_1 : IsSimpleRing K} {inst_2 : CommRing L}   {in
st_3 : Algebra K L} …
-/
theorem comap_eq : w.comap (algebraMap K L) = v := by
  ext
  simpa only [coe_apply] using! AbsoluteValue.ext_iff.1 (LiesOver.comp_eq w.1 v.1) _
/-
**NumberField.InfinitePlace.LiesOver.mk_embedding_comp** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.InfinitePlace.LiesOver`。
形式化陈述：mk_embedding_comp : InfinitePlace.mk (w.embedding.comp (algebraMap K L)) =
 v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
-/
theorem mk_embedding_comp : InfinitePlace.mk (w.embedding.comp (algebraMap K L)) = v := by
  rw [← comap_mk, w.mk_embedding, comap_eq w v]

/-- If `w : InfinitePlace L` lies above `v : InfinitePlace K`, then either `w.embedding`
extends `v.embedding` as complex embeddings, or `conjugate w.embedding` extends `v.embedding`. -/
/-
**NumberField.InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_co
mp_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.LiesOver`。
形式化陈述：embedding_comp_eq_or_conjugate_embedding_comp_eq : w.embedding.comp (algeb
raMap K L) = v.embedding ∨ (conjugate w.embedding).comp (algebraMap K L) = v.emb
edding
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq`：embedding_mk_eq (φ : K ->+* C
omplex) : embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.LiesOver.mk_embedding_comp`：mk_embedding_comp 
: InfinitePlace.mk (w.embedding.comp (algebraMap K L)) = v

--- 原说明 ---
If `w : InfinitePlace L` lies above `v : InfinitePlace K`, then either `w.embedd
ing`
extends `v.embedding` as complex embeddings, or `conjugate w.embedding` extends 
`v.embedding`.
-/
theorem embedding_comp_eq_or_conjugate_embedding_comp_eq :
    w.embedding.comp (algebraMap K L) = v.embedding ∨
      (conjugate w.embedding).comp (algebraMap K L) = v.embedding := by
  cases embedding_mk_eq (w.embedding.comp (algebraMap K L)) with
  | inl hl => exact .inl (hl ▸ congrArg embedding (mk_embedding_comp w v))
  | inr hr => simpa using .inr (hr ▸ congrArg embedding (mk_embedding_comp w v))

variable {v}

/-- If `w : InfinitePlace L` lies above `v : InfinitePlace K` and `v` is complex, then so is `w`. -/
/-
**NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.InfinitePlace.LiesOver`。
形式化陈述：isComplex_of_isComplex_under (hv : v.IsComplex) : w.IsComplex
参数：hv : v.IsComplex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.isComplex_iff`：isComplex_iff {w : InfinitePlac
e K} : IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.ComplexEmbedding.isReal_iff`：isReal_iff {φ : K ->+* Complex}
 : IsReal φ ↔ conjugate φ = φ
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq`：embedding_mk_eq (φ : K ->+* C
omplex) : embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NumberField.InfinitePlace.comap_mk`：comap_mk (φ : K ->+* Complex) (f : k
 ->+* K) : (mk φ).comap f = mk (φ.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r

--- 原说明 ---
If `w : InfinitePlace L` lies above `v : InfinitePlace K` and `v` is complex, th
en so is `w`.
-/
theorem isComplex_of_isComplex_under (hv : v.IsComplex) : w.IsComplex := by
  rw [isComplex_iff, ComplexEmbedding.isReal_iff, RingHom.ext_iff, not_forall] at hv ⊢
  obtain ⟨x, hx⟩ := hv
  use algebraMap K L x
  rw [← comap_eq w v, ← mk_embedding w, comap_mk] at hx
  rcases embedding_mk_eq (w.embedding.comp (algebraMap K L)) with (_ | _) <;> aesop

/-- If `w : InfinitePlace L` lies above `v : InfinitePlace K` and `w` is real, then so is `v`. -/
/-
**NumberField.InfinitePlace.LiesOver.isReal_of_isReal_over** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.InfinitePlace.LiesOver`。
形式化陈述：isReal_of_isReal_over (hw : w.IsReal) : v.IsReal
参数：hw : w.IsReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.not_isComplex_iff_isReal`：not_isComplex_iff_is
Real {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under`：isCompl
ex_of_isComplex_under (hv : v.IsComplex) : w.IsComplex

--- 原说明 ---
If `w : InfinitePlace L` lies above `v : InfinitePlace K` and `w` is real, then 
so is `v`.
-/
theorem isReal_of_isReal_over (hw : w.IsReal) : v.IsReal := by
  rw [← not_isComplex_iff_isReal] at hw ⊢
  exact mt (isComplex_of_isComplex_under w) hw

end LiesOver

/-
**NumberField.InfinitePlace.IsRamified.liesOver_isReal_under** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.InfinitePlace.IsRamified`。
形式化陈述：∀ {K : Type u_4} {L : Type u_5} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L]   (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePl
ace K) [w.LiesOver v],   NumberField.InfinitePlace.IsRamified K w → v.IsReal
参数：w : NumberField.InfinitePlace L；v : NumberField.InfinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isRamified_iff`：isRamified_iff : w.IsRamified 
k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
-/
theorem IsRamified.liesOver_isReal_under (hw : w.IsRamified K) :
    v.IsReal := LiesOver.comap_eq w v ▸ (isRamified_iff.1 hw).2
/-
**NumberField.InfinitePlace.IsUnramified.liesOver_isReal_over** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.InfinitePlace.IsUnramified`。
形式化陈述：∀ {K : Type u_4} {L : Type u_5} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L]   (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePl
ace K) [w.LiesOver v],   NumberField.InfinitePlace.IsUnramified K w → v.IsReal →
 w.IsReal
参数：w : NumberField.InfinitePlace L；v : NumberField.InfinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `NumberField.InfinitePlace.isUnramified_iff`：isUnramified_iff : IsUnramif
ied k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isComplex_iff_isReal`：not_isComplex_iff_is
Real {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w
-/
theorem IsUnramified.liesOver_isReal_over (hw : w.IsUnramified K) (hv : v.IsReal) : w.IsReal :=
  (InfinitePlace.isUnramified_iff.1 hw).resolve_right
    (by simpa [LiesOver.comap_eq w v] using not_isComplex_iff_isReal.2 hv)

end LiesOver

section placesOver

variable (v : InfinitePlace K) (L)

/-- The set of infinite places of `L` that lie above a given infinite place of `K`. -/
/-
**NumberField.InfinitePlace.placesOver** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.In
finitePlace`。
形式化陈述：placesOver : Set (InfinitePlace L)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of infinite places of `L` that lie above a given infinite place of `K`.
-/
def placesOver : Set (InfinitePlace L) := { w | w.LiesOver v }

/-- The set of infinite places of `L` that are unramified over a given infinite place of `K`. -/
/-
**NumberField.InfinitePlace.unramifiedPlacesOver** 是 Mathlib 中的一个定义，位于命名空间 `Numb
erField.InfinitePlace`。
形式化陈述：unramifiedPlacesOver : Set (InfinitePlace L)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of infinite places of `L` that are unramified over a given infinite plac
e of `K`.
-/
def unramifiedPlacesOver : Set (InfinitePlace L) := { w | w.LiesOver v ∧ w.IsUnramified K }

/-- The set of infinite places of `L` that are ramified over a given infinite place of `K`. -/
/-
**NumberField.InfinitePlace.ramifiedPlacesOver** 是 Mathlib 中的一个定义，位于命名空间 `Number
Field.InfinitePlace`。
形式化陈述：ramifiedPlacesOver : Set (InfinitePlace L)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of infinite places of `L` that are ramified over a given infinite place 
of `K`.
-/
def ramifiedPlacesOver : Set (InfinitePlace L) := { w | w.LiesOver v ∧ w.IsRamified K }

variable {L} {v} {w : InfinitePlace L}
/-
**NumberField.InfinitePlace.mk_mem_unramifiedPlacesOver** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.InfinitePlace`。
形式化陈述：mk_mem_unramifiedPlacesOver {φ : L ->+* Complex} (h : φ in unmixedEmbeddin
gsOver L (v.embedding)) : mk φ in unramifiedPlacesOver L v
参数：h : φ in unmixedEmbeddingsOver L (v.embedding)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `AbsoluteValue.LiesOver.comp_eq`：∀ {K : Type u_3} {L : Type u_4} {S : Typ
e u_5} {inst : CommRing K} {inst_1 : IsSimpleRing K} {inst_2 : CommRing L}   {in
st_3 : Algebra K L} …
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `NumberField.InfinitePlace.LiesOver.instLiesOverRealValAbsoluteValueExist
sRingHomComplexEqPlaceMkOfLiesOver`：∀ {K : Type u_4} {L : Type u_5} [inst : Fiel
d K] [inst_1 : Field L] [inst_2 : Algebra K L] {φ : K →+* ℂ} {ψ : L →+* ℂ}   [Nu
mberField.Comple…
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `NumberField.ComplexEmbedding.IsUnmixed.mk_isUnramified`：∀ {k : Type u_1}
 [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K] {φ : 
K →+* ℂ},   NumberField.ComplexEmbedding.IsU…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mk_mem_unramifiedPlacesOver {φ : L →+* ℂ} (h : φ ∈ unmixedEmbeddingsOver L (v.embedding)) :
    mk φ ∈ unramifiedPlacesOver L v :=
  ⟨⟨have := h.1; mk_embedding v ▸ LiesOver.comp_eq (mk φ).1 (mk v.embedding).1⟩,
    h.2.mk_isUnramified⟩
/-
**NumberField.InfinitePlace.liesOver_embedding_of_mem_ramifiedPlacesOver** 是 Mat
hlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：liesOver_embedding_of_mem_ramifiedPlacesOver (hw : w in ramifiedPlacesOver
 L v) : ComplexEmbedding.LiesOver w.embedding v.embedding where over
参数：hw : w in ramifiedPlacesOver L v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
· 使用定理 `NumberField.InfinitePlace.IsRamified.comap_embedding`：∀ {k : Type u_1} [
inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : 
NumberField.InfinitePlace K},   NumberFiel…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem liesOver_embedding_of_mem_ramifiedPlacesOver (hw : w ∈ ramifiedPlacesOver L v) :
    ComplexEmbedding.LiesOver w.embedding v.embedding where
  over := have := hw.1; hw.2.comap_embedding ▸ congrArg embedding (LiesOver.comap_eq w v)
/-
**NumberField.InfinitePlace.liesOver_conjugate_embedding_of_mem_ramifiedPlacesOv
er** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver (hw : w in ramified
PlacesOver L v) : ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding 
where over
参数：hw : w in ramifiedPlacesOver L v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
· 使用定理 `NumberField.InfinitePlace.IsRamified.comap_embedding_conjugate`：∀ {k : T
ype u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k 
K]   {w : NumberField.InfinitePlace K},   NumberFiel…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver
    (hw : w ∈ ramifiedPlacesOver L v) :
    ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding where
  over := have := hw.1; hw.2.comap_embedding_conjugate ▸ congrArg embedding (LiesOver.comap_eq w v)
/-
**NumberField.InfinitePlace.mk_mem_ramifiedPlacesOver** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
形式化陈述：mk_mem_ramifiedPlacesOver {φ : L ->+* Complex} (h : φ in mixedEmbeddingsOv
er L (v.embedding)) : mk φ in ramifiedPlacesOver L v
参数：h : φ in mixedEmbeddingsOver L (v.embedding)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `AbsoluteValue.LiesOver.comp_eq`：∀ {K : Type u_3} {L : Type u_4} {S : Typ
e u_5} {inst : CommRing K} {inst_1 : IsSimpleRing K} {inst_2 : CommRing L}   {in
st_3 : Algebra K L} …
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `NumberField.InfinitePlace.LiesOver.instLiesOverRealValAbsoluteValueExist
sRingHomComplexEqPlaceMkOfLiesOver`：∀ {K : Type u_4} {L : Type u_5} [inst : Fiel
d K] [inst_1 : Field L] [inst_2 : Algebra K L] {φ : K →+* ℂ} {ψ : L →+* ℂ}   [Nu
mberField.Comple…
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `NumberField.ComplexEmbedding.IsMixed.mk_isRamified`：∀ {k : Type u_1} [in
st : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K] {φ : K →+
* ℂ},   NumberField.ComplexEmbedding.IsM…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mk_mem_ramifiedPlacesOver {φ : L →+* ℂ} (h : φ ∈ mixedEmbeddingsOver L (v.embedding)) :
    mk φ ∈ ramifiedPlacesOver L v :=
  ⟨⟨have := h.1; mk_embedding v ▸ LiesOver.comp_eq (mk φ).1 (mk v.embedding).1⟩, h.2.mk_isRamified⟩

variable (w)
/-
**NumberField.InfinitePlace.embedding_mem_mixedEmbeddingsOver** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：embedding_mem_mixedEmbeddingsOver (hw : w in ramifiedPlacesOver L v) : w.e
mbedding in mixedEmbeddingsOver L (v.embedding)
参数：hw : w in ramifiedPlacesOver L v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.liesOver_embedding_of_mem_ramifiedPlacesOver`：
liesOver_embedding_of_mem_ramifiedPlacesOver (hw : w in ramifiedPlacesOver L v) 
: ComplexEmbedding.LiesOver w.embedding v.embedding where ov…
· 使用定理 `NumberField.InfinitePlace.IsRamified.isMixed_embedding`：∀ {k : Type u_1}
 [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w 
: NumberField.InfinitePlace K},   NumberFiel…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem embedding_mem_mixedEmbeddingsOver (hw : w ∈ ramifiedPlacesOver L v) :
    w.embedding ∈ mixedEmbeddingsOver L (v.embedding) :=
  ⟨liesOver_embedding_of_mem_ramifiedPlacesOver hw, hw.2.isMixed_embedding⟩
/-
**NumberField.InfinitePlace.conjugate_embedding_mem_mixedEmbeddingsOver** 是 Math
lib 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：conjugate_embedding_mem_mixedEmbeddingsOver (hw : w in ramifiedPlacesOver 
L v) : conjugate w.embedding in mixedEmbeddingsOver L (v.embedding)
参数：hw : w in ramifiedPlacesOver L v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.liesOver_conjugate_embedding_of_mem_ramifiedPl
acesOver`：liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver (hw : w in rami
fiedPlacesOver L v) : ComplexEmbedding.LiesOver (conjugate w.embedding…
· 使用定理 `NumberField.InfinitePlace.IsRamified.isMixed_conjugate_embedding`：∀ {k :
 Type u_1} [inst : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra 
k K]   {w : NumberField.InfinitePlace K},   NumberFiel…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem conjugate_embedding_mem_mixedEmbeddingsOver (hw : w ∈ ramifiedPlacesOver L v) :
    conjugate w.embedding ∈ mixedEmbeddingsOver L (v.embedding) :=
  ⟨liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver hw, hw.2.isMixed_conjugate_embedding⟩

variable (L) (v)
/-
**NumberField.InfinitePlace.disjoint_ramifiedPlacesOver_unramifiedPlacesOver** 是
 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：disjoint_ramifiedPlacesOver_unramifiedPlacesOver : Disjoint (ramifiedPlace
sOver L v) (unramifiedPlacesOver L v)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_ramifiedPlacesOver_unramifiedPlacesOver :
    Disjoint (ramifiedPlacesOver L v) (unramifiedPlacesOver L v) := by
  grind [ramifiedPlacesOver, unramifiedPlacesOver]
/-
**NumberField.InfinitePlace.union_ramifiedPlacesOver_unramifiedPlacesOver** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：union_ramifiedPlacesOver_unramifiedPlacesOver : (ramifiedPlacesOver L v) u
nion (unramifiedPlacesOver L v) = placesOver L v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.placesOver.eq_1`：∀ {K : Type u_4} (L : Type u_
5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   (v : NumberField
.InfinitePlace K), NumberField.…
· 使用定理 `NumberField.InfinitePlace.ramifiedPlacesOver.eq_1`：∀ {K : Type u_4} (L :
 Type u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   (v : Num
berField.InfinitePlace K),   NumberFiel…
· 使用定理 `NumberField.InfinitePlace.unramifiedPlacesOver.eq_1`：∀ {K : Type u_4} (L
 : Type u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   (v : N
umberField.InfinitePlace K),   NumberFiel…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ofPred_or`：ofPred_or {p q : α -> Prop} : { a | p a ∨ q a } = { a | p
 a } union { a | q a }
-/
theorem union_ramifiedPlacesOver_unramifiedPlacesOver :
    (ramifiedPlacesOver L v) ∪ (unramifiedPlacesOver L v) = placesOver L v := by
  rw [placesOver, ramifiedPlacesOver, unramifiedPlacesOver, ← Set.ofPred_or]
  grind
/-
**NumberField.InfinitePlace.bijOn_sumElim_conjugate** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.InfinitePlace`。
形式化陈述：bijOn_sumElim_conjugate : (Set.sumEquiv.symm (ramifiedPlacesOver L v, rami
fiedPlacesOver L v)).BijOn (Sum.elim embedding (conjugate ∘ embedding)) (mixedEm
beddingsOver L v.embedding)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.sumElim`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : 
α → γ} {g : β → γ} {s : Set α × Set β} {t : Set γ},   Set.MapsTo f s.1 t → Set.M
apsTo g …
· 使用定理 `NumberField.InfinitePlace.embedding_mem_mixedEmbeddingsOver`：embedding_m
em_mixedEmbeddingsOver (hw : w in ramifiedPlacesOver L v) : w.embedding in mixed
EmbeddingsOver L (v.embedding)
· 使用定理 `NumberField.InfinitePlace.conjugate_embedding_mem_mixedEmbeddingsOver`：c
onjugate_embedding_mem_mixedEmbeddingsOver (hw : w in ramifiedPlacesOver L v) : 
conjugate w.embedding in mixedEmbeddingsOver L (v.embedding…
· 使用定理 `Set.InjOn.sumElim`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α
 → γ} {g : β → γ} {s : Set α × Set β},   Set.InjOn f s.1 → Set.InjOn g s.2 → (∀ 
a ∈ s.1…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `NumberField.InfinitePlace.embedding_injective`：embedding_injective : (em
bedding (K
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `star_injective`：star_injective [InvolutiveStar R] : Function.Injective (
star : R -> R)
· 使用定理 `NumberField.InfinitePlace.IsRamified.ne_conjugate`：∀ {k : Type u_1} [ins
t : Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w₁ w₂ :
 NumberField.InfinitePlace K},   Number…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq`：embedding_mk_eq (φ : K ->+* C
omplex) : embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `NumberField.InfinitePlace.mk_mem_ramifiedPlacesOver`：mk_mem_ramifiedPlac
esOver {φ : L ->+* Complex} (h : φ in mixedEmbeddingsOver L (v.embedding)) : mk 
φ in ramifiedPlacesOver L v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bijOn_sumElim_conjugate :
    (Set.sumEquiv.symm (ramifiedPlacesOver L v, ramifiedPlacesOver L v)).BijOn
      (Sum.elim embedding (conjugate ∘ embedding)) (mixedEmbeddingsOver L v.embedding) :=
  ⟨.sumElim embedding_mem_mixedEmbeddingsOver conjugate_embedding_mem_mixedEmbeddingsOver,
    (embedding_injective L).injOn.sumElim (star_injective.comp (embedding_injective L)).injOn
      (fun _ _ _ h ↦ h.2.ne_conjugate), fun ψ h ↦ by cases embedding_mk_eq ψ with
        | inl hl => simpa using .inl ⟨mk ψ, mk_mem_ramifiedPlacesOver h, hl⟩
        | inr hr => simpa using .inr ⟨mk ψ, mk_mem_ramifiedPlacesOver h, by aesop⟩⟩

/-- The number of mixed embeddings over an infinite place is twice the number of ramified places
over the place. -/
/-
**NumberField.InfinitePlace.ramifiedPlacesOver_ncard** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.InfinitePlace`。
形式化陈述：ramifiedPlacesOver_ncard : 2 * (ramifiedPlacesOver L v).ncard = (mixedEmbe
ddingsOver L v.embedding).ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.BijOn.ncard_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α →
 β} {t : Set β}, Set.BijOn f s t → s.ncard = t.ncard
· 使用定理 `NumberField.InfinitePlace.bijOn_sumElim_conjugate`：bijOn_sumElim_conjuga
te : (Set.sumEquiv.symm (ramifiedPlacesOver L v, ramifiedPlacesOver L v)).BijOn 
(Sum.elim embedding (conjugate ∘ embedd…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Set.ncard_sumEquiv_symm_apply`：ncard_sumEquiv_symm_apply {α : Type*} (s 
: Set α) : (Set.sumEquiv.symm (s, s)).ncard = s.ncard + s.ncard

--- 原说明 ---
The number of mixed embeddings over an infinite place is twice the number of ram
ified places
over the place.
-/
theorem ramifiedPlacesOver_ncard :
    2 * (ramifiedPlacesOver L v).ncard = (mixedEmbeddingsOver L v.embedding).ncard := by
  rw [← (bijOn_sumElim_conjugate L v).ncard_eq, two_mul, Set.ncard_sumEquiv_symm_apply]

variable {L}

open scoped Classical in
/-- Function sending `w : InfinitePlace L` to `w.embedding` if `w.embedding` lies over
`v.embedding`, otherwise to its conjugate. -/
/-
**NumberField.InfinitePlace.embeddingConjugateIte** 是 Mathlib 中的一个定义，位于命名空间 `Num
berField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function sending `w : InfinitePlace L` to `w.embedding` if `w.embedding` lies ov
er
`v.embedding`, otherwise to its conjugate.
-/
private noncomputable def embeddingConjugateIte : L →+* ℂ :=
  if ComplexEmbedding.LiesOver w.embedding v.embedding then w.embedding else conjugate w.embedding

variable {v w}
/-
**NumberField.InfinitePlace.embeddingConjugateIte_pos** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem embeddingConjugateIte_pos (h : ComplexEmbedding.LiesOver w.embedding v.embedding) :
    embeddingConjugateIte v w = w.embedding := by simp [embeddingConjugateIte, h]
/-
**NumberField.InfinitePlace.embeddingConjugateIte_neg** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem embeddingConjugateIte_neg (h : ¬ComplexEmbedding.LiesOver w.embedding v.embedding) :
    embeddingConjugateIte v w = conjugate w.embedding := by simp [embeddingConjugateIte, h]

variable (L v)
/-
**NumberField.InfinitePlace.mapsTo_embeddingConjugateIte** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mapsTo_embeddingConjugateIte : (unramifiedPlacesOver L v).MapsTo
    (embeddingConjugateIte v) (unmixedEmbeddingsOver L v.embedding) := by
  rintro w ⟨_, hw⟩
  by_cases h : ComplexEmbedding.LiesOver w.embedding v.embedding
  · simpa [embeddingConjugateIte_pos h] using ⟨h, hw.isUnmixed⟩
  · simpa [embeddingConjugateIte_neg h] using
      ⟨⟨(LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v).resolve_left
        (liesOver_iff.not.1 h)⟩, hw.isUnmixed_conjugate⟩
/-
**NumberField.InfinitePlace.surjOn_embeddingConjugateIte** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem surjOn_embeddingConjugateIte : (unramifiedPlacesOver L v).SurjOn
    (embeddingConjugateIte v) (unmixedEmbeddingsOver L v.embedding) := by
  refine fun ψ h ↦ ⟨mk ψ, mk_mem_unramifiedPlacesOver h, ?_⟩
  rcases embedding_mk_eq ψ with (_ | hψ)
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver])
  · simpa [embeddingConjugateIte, hψ] using fun ⟨_⟩ ↦
      h.2.isReal_iff_isReal.1 <| by have := h.1.over; aesop

open scoped Classical in
/-
**NumberField.InfinitePlace.bijOn_extensionIte** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bijOn_extensionIte : (unramifiedPlacesOver L v).BijOn (embeddingConjugateIte v)
    (unmixedEmbeddingsOver L v.embedding) :=
  ⟨mapsTo_embeddingConjugateIte L v, ((embedding_injective _).ite (star_injective.comp
    (embedding_injective _)) (fun _ _ ↦ eq_of_embedding_eq_conjugate L)).injOn,
      surjOn_embeddingConjugateIte L v⟩

/-- The number of unramified places over an infinite place is equal to the number of unmixed
embeddings over the place. -/
/-
**NumberField.InfinitePlace.unramifiedPlacesOver_ncard** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.InfinitePlace`。
形式化陈述：unramifiedPlacesOver_ncard : (unramifiedPlacesOver L v).ncard = (unmixedEm
beddingsOver L v.embedding).ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.BijOn.ncard_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α →
 β} {t : Set β}, Set.BijOn f s t → s.ncard = t.ncard
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification.0.N
umberField.InfinitePlace.bijOn_extensionIte`：∀ {K : Type u_4} (L : Type u_5) [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   (v : NumberField.Infin
itePlace K),   Set.BijOn …

--- 原说明 ---
The number of unramified places over an infinite place is equal to the number of
 unmixed
embeddings over the place.
-/
theorem unramifiedPlacesOver_ncard :
    (unramifiedPlacesOver L v).ncard = (unmixedEmbeddingsOver L v.embedding).ncard := by
  rw [(bijOn_extensionIte L v).ncard_eq]

open Finset in
/-- The degree of `L` over `K` is equal to the number of unramified places over `v` plus twice the
number of ramified places over `v`. -/
/-
**NumberField.InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：unramifedPlacesOver_ncard_add_eq_finrank [NumberField K] [NumberField L] :
 (unramifiedPlacesOver L v).ncard + 2 * (ramifiedPlacesOver L v).ncard = Module.
finrank K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NumberField.instFiniteDimensional`：∀ (K : Type u_1) (L : Type u_2) [inst
 : Field K] [inst_1 : Field L] [NumberField K] [NumberField L]   [inst_4 : Algeb
ra K L], FiniteDimensio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.card`：AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra 
F K] : Fintype.card (E ->ₐ[F] K) = finrank F E
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.InfinitePlace.ramifiedPlacesOver_ncard`：ramifiedPlacesOver_n
card : 2 * (ramifiedPlacesOver L v).ncard = (mixedEmbeddingsOver L v.embedding).
ncard
· 使用定理 `NumberField.InfinitePlace.unramifiedPlacesOver_ncard`：unramifiedPlacesOv
er_ncard : (unramifiedPlacesOver L v).ncard = (unmixedEmbeddingsOver L v.embeddi
ng).ncard
· 使用定理 `Set.ncard_union_eq`：ncard_union_eq (h : Disjoint s t) (hs : s.Finite
· 使用定理 `NumberField.ComplexEmbedding.disjoint_unmixedEmbeddingsOver_mixedEmbeddi
ngsOver`：disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver : Disjoint (unmixedE
mbeddingsOver L ψ) (mixedEmbeddingsOver L ψ)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.ComplexEmbedding.union_unmixedEmbeddingsOver_mixedEmbeddings
Over`：union_unmixedEmbeddingsOver_mixedEmbeddingsOver : (unmixedEmbeddingsOver L
 ψ) union (mixedEmbeddingsOver L ψ) = { φ | ComplexEmbedding.LiesO…
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用引理 `Finset.card_nbij`：card_nbij (i : α -> β) (hi : Set.MapsTo i s t) (i_inj 
: (s : Set α).InjOn i) (i_surj : (s : Set α).SurjOn i t) : #s = #t
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Finite.toFinset_ofPred`：∀ {α : Type u} [inst : Fintype α] (p : α → P
rop) [inst_1 : DecidablePred p] (h : {x | p x}.Finite),   h.toFinset = {x | p x}
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NumberField.ComplexEmbedding.LiesOver.over`：∀ {K : Type u_3} {L : Type u
_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} (φ : L →+* ℂ) (ψ 
: K →+* ℂ)   [self : NumberField…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The degree of `L` over `K` is equal to the number of unramified places over `v` 
plus twice the
number of ramified places over `v`.
-/
theorem unramifedPlacesOver_ncard_add_eq_finrank [NumberField K] [NumberField L] :
    (unramifiedPlacesOver L v).ncard + 2 * (ramifiedPlacesOver L v).ncard = Module.finrank K L := by
  classical
  let : Algebra K ℂ := v.embedding.toAlgebra
  rw [← AlgHom.card K L ℂ, ramifiedPlacesOver_ncard, unramifiedPlacesOver_ncard,
    ← Set.ncard_union_eq (disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver L v.embedding),
    union_unmixedEmbeddingsOver_mixedEmbeddingsOver, Set.ncard_eq_toFinset_card]
  apply (card_nbij AlgHom.toRingHom (fun σ _ ↦ by simpa using ⟨by aesop⟩)
    AlgHom.coe_ringHom_injective.injOn (fun ψ hψ ↦ ?_)).symm
  simp only [Set.Finite.toFinset_ofPred, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hψ
  exact ⟨⟨ψ, fun _ ↦ by simp [RingHom.algebraMap_toAlgebra, ← hψ.over]⟩, by simp⟩

end placesOver

end NumberField.InfinitePlace

