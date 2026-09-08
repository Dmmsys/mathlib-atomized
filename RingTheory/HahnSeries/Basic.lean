/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Order.WellFoundedSet

/-!
# Hahn Series

If `Γ` is ordered and `R` has zero, then the type `HahnSeries Γ R`, which we denote as `R⟦Γ⟧`,
consists of formal series over `Γ` with coefficients in `R`, whose supports are partially
well-ordered. With further structure on `R` and `Γ`, we can add further structure on `R⟦Γ⟧`, with
the most studied case being when `Γ` is a linearly ordered abelian group and `R` is a field, in
which case `R⟦Γ⟧` is a valued field, with value group `Γ`.

These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `Mathlib/RingTheory/LaurentSeries.lean`.

## Main Definitions

* If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
* `support x` is the subset of `Γ` whose coefficients are nonzero.
* `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
* `orderTop x` is a minimal element of `WithTop Γ` where `x` has a nonzero
  coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
* `order x` is a minimal element of `Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is zero
  when `x = 0`.
* `map` takes each coefficient of a Hahn series to its target under a zero-preserving map.
* `embDomain` preserves coefficients, but embeds the index set `Γ` in a larger poset.

## References

- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function

noncomputable section

/-- If `Γ` is linearly ordered and `R` has zero, then `R⟦Γ⟧` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
/-
**HahnSeries** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Γ : Type u_1) → (R : Type u_2) → [PartialOrder Γ] → [Zero R] → Type (max 
u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Γ` is linearly ordered and `R` has zero, then `R⟦Γ⟧` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-found
ed.
-/
structure HahnSeries (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R] where
  /-- The coefficient function of a Hahn Series. -/
  coeff : Γ → R
  isPWO_support' : (Function.support coeff).IsPWO

variable {Γ Γ' R S : Type*}

namespace HahnSeries

@[inherit_doc HahnSeries]
scoped syntax:max (priority := high) term noWs "⟦" term "⟧" : term

macro_rules | `($R⟦$M⟧) => `(HahnSeries $M $R)

/-- Unexpander for `HahnSeries`. -/
@[scoped app_unexpander HahnSeries]
meta def unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $M $R) => `($R⟦$M⟧)
  | _ => throw ()

section Zero

variable [PartialOrder Γ] [Zero R]

/-
**HahnSeries.coeff_injective** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_injective : Injective (coeff : R⟦Γ⟧ -> Γ -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
-/
theorem coeff_injective : Injective (coeff : R⟦Γ⟧ → Γ → R) :=
  fun _ _ => HahnSeries.ext

@[simp]
/-
**HahnSeries.coeff_inj** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_inj {x y : R⟦Γ⟧} : x.coeff = y.coeff ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `HahnSeries.coeff_injective`：coeff_injective : Injective (coeff : R⟦Γ⟧ ->
 Γ -> R)
-/
theorem coeff_inj {x y : R⟦Γ⟧} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
nonrec def support (x : R⟦Γ⟧) : Set Γ :=
  support x.coeff

@[simp]
/-
**HahnSeries.support_mk** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_mk (f : Γ -> R) (h) : support ⟨f, h⟩ = Function.support f
参数：f : Γ -> R；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_mk (f : Γ → R) (h) : support ⟨f, h⟩ = Function.support f :=
  rfl

@[simp]
/-
**HahnSeries.isPWO_support** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
参数：x : R⟦Γ⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isPWO_support'`：∀ {Γ : Type u_1} {R : Type u_2} [inst : Parti
alOrder Γ] [inst_1 : Zero R] (self : HahnSeries Γ R),   (Function.support self.c
oeff).IsPWO
-/
theorem isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO :=
  x.isPWO_support'

@[simp]
/-
**HahnSeries.isWF_support** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
参数：x : R⟦Γ⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPW
O → s.IsWF
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
-/
theorem isWF_support (x : R⟦Γ⟧) : x.support.IsWF :=
  x.isPWO_support.isWF

@[simp]
/-
**HahnSeries.mem_support** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support ↔ x.coeff a != 0
参数：x : R⟦Γ⟧；a : Γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support (x : R⟦Γ⟧) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 :=
  .rfl
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero R⟦Γ⟧ :=
  ⟨{  coeff := 0
      isPWO_support' := by simp }⟩
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited R⟦Γ⟧ :=
  ⟨0⟩
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton R] : Subsingleton R⟦Γ⟧ :=
  ⟨fun _ _ => HahnSeries.ext (by subsingleton)⟩
/-
**HahnSeries.coeff_zero'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_zero' : (0 : R⟦Γ⟧).coeff = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_zero' : (0 : R⟦Γ⟧).coeff = 0 :=
  rfl

@[simp]
/-
**HahnSeries.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_zero {a : Γ} : (0 : R⟦Γ⟧).coeff a = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_zero {a : Γ} : (0 : R⟦Γ⟧).coeff a = 0 :=
  rfl

@[simp]
/-
**HahnSeries.coeff_fun_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_fun_eq_zero_iff {x : R⟦Γ⟧} : x.coeff = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `HahnSeries.coeff_injective`：coeff_injective : Injective (coeff : R⟦Γ⟧ ->
 Γ -> R)
-/
theorem coeff_fun_eq_zero_iff {x : R⟦Γ⟧} : x.coeff = 0 ↔ x = 0 :=
  coeff_injective.eq_iff' rfl
/-
**HahnSeries.ne_zero_of_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ne_zero_of_coeff_ne_zero {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x != 0
参数：h : x.coeff g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `HahnSeries.coeff_zero`：coeff_zero {a : Γ} : (0 : R⟦Γ⟧).coeff a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_coeff_ne_zero {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g ≠ 0) : x ≠ 0 :=
  mt (fun x0 => (x0.symm ▸ coeff_zero : x.coeff g = 0)) h

@[simp]
/-
**HahnSeries.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_zero : support (0 : R⟦Γ⟧) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_zero`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M], 
Function.support 0 = ∅
-/
theorem support_zero : support (0 : R⟦Γ⟧) = ∅ :=
  Function.support_zero

@[simp]
nonrec theorem support_nonempty_iff {x : R⟦Γ⟧} : x.support.Nonempty ↔ x ≠ 0 := by
  rw [support, support_nonempty_iff, Ne, coeff_fun_eq_zero_iff]

@[simp]
/-
**HahnSeries.support_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_eq_empty_iff {x : R⟦Γ⟧} : x.support = ∅ ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.support_eq_empty_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Z
ero M] {f : ι → M}, Function.support f = ∅ ↔ f = 0
· 使用定理 `HahnSeries.coeff_fun_eq_zero_iff`：coeff_fun_eq_zero_iff {x : R⟦Γ⟧} : x.c
oeff = 0 ↔ x = 0
-/
theorem support_eq_empty_iff {x : R⟦Γ⟧} : x.support = ∅ ↔ x = 0 :=
  Function.support_eq_empty_iff.trans coeff_fun_eq_zero_iff

/-- The map of Hahn series induced by applying a zero-preserving map to each coefficient. -/
@[simps]
/-
**HahnSeries.map** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：map [Zero S] (x : R⟦Γ⟧) {F : Type*} [FunLike F R S] [ZeroHomClass F R S] (
f : F) : S⟦Γ⟧ where coeff g
参数：x : R⟦Γ⟧；f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map of Hahn series induced by applying a zero-preserving map to each coeffic
ient.
-/
def map [Zero S] (x : R⟦Γ⟧) {F : Type*} [FunLike F R S] [ZeroHomClass F R S] (f : F) : S⟦Γ⟧ where
  coeff g := f (x.coeff g)
  isPWO_support' := x.isPWO_support.mono <| Function.support_comp_subset (ZeroHomClass.map_zero f) _

@[simp]
/-
**HahnSeries.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [inst : PartialOrder Γ] [in
st_1 : Zero R] [inst_2 : Zero S]   (f : ZeroHom R S), HahnSeries.map 0 f = 0
参数：f : ZeroHom R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.map_coeff`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [in
st : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x : HahnSeries Γ R) 
{F : Type …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_zero [Zero S] (f : ZeroHom R S) : (0 : R⟦Γ⟧).map f = 0 := by
  ext; simp
/-
**HahnSeries.support_map_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_map_subset [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S) : (x.map f).suppo
rt subseteq x.support
参数：x : R⟦Γ⟧；f : ZeroHom R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_comp_subset`：∀ {ι : Type u_1} {M : Type u_3} {N : Type 
u_4} [inst : Zero M] [inst_1 : Zero N] {g : M → N},   g 0 = 0 → ∀ (f : ι → M), F
unction.support (g…
· 使用定理 `ZeroHomClass.map_zero`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N :
 outParam (Type u_12)} {inst : Zero M} {inst_1 : Zero N}   {inst_2 : FunLike F M
 N} [self :…
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
-/
theorem support_map_subset [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S) :
    (x.map f).support ⊆ x.support :=
  Function.support_comp_subset (ZeroHomClass.map_zero f) _

/-- Change a `HahnSeries` with coefficients in a `HahnSeries` to a `HahnSeries` on a Lex product. -/
/-
**HahnSeries.ofIterate** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：ofIterate [PartialOrder Γ'] (x : R⟦Γ'⟧⟦Γ⟧) : R⟦Γ ×ₗ Γ'⟧ where coeff
参数：x : R⟦Γ'⟧⟦Γ⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change a `HahnSeries` with coefficients in a `HahnSeries` to a `HahnSeries` on a
 Lex product.
-/
def ofIterate [PartialOrder Γ'] (x : R⟦Γ'⟧⟦Γ⟧) : R⟦Γ ×ₗ Γ'⟧ where
  coeff := fun g => coeff (coeff x g.1) g.2
  isPWO_support' := by
    refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
    · refine Set.IsPWO.mono x.isPWO_support' ?_
      simp_rw [Set.image_subset_iff, support_subset_iff, Set.mem_preimage, Function.mem_support]
      exact fun _ ↦ ne_zero_of_coeff_ne_zero
    · exact fun a => by simpa [Function.mem_support, ne_eq] using! (x.coeff a).isPWO_support'

@[simp]
/-
**HahnSeries.mk_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `HahnSeries`。
形式化陈述：mk_eq_zero (f : Γ -> R) (h) : HahnSeries.mk f h = 0 ↔ f = 0
参数：f : Γ -> R；h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mk_eq_zero (f : Γ → R) (h) : HahnSeries.mk f h = 0 ↔ f = 0 := by
  simp_rw [HahnSeries.ext_iff, funext_iff, coeff_zero, Pi.zero_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Change a `HahnSeries` on a Lex product to a `HahnSeries` with coefficients in a `HahnSeries`. -/
/-
**HahnSeries.toIterate** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：toIterate [PartialOrder Γ'] (x : R⟦Γ ×ₗ Γ'⟧) : R⟦Γ'⟧⟦Γ⟧ where coeff
参数：x : R⟦Γ ×ₗ Γ'⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change a `HahnSeries` on a Lex product to a `HahnSeries` with coefficients in a 
`HahnSeries`.
-/
def toIterate [PartialOrder Γ'] (x : R⟦Γ ×ₗ Γ'⟧) : R⟦Γ'⟧⟦Γ⟧ where
  coeff := fun g => {
    coeff := fun g' => coeff x (g, g')
    isPWO_support' := Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g
  }
  isPWO_support' := by
    have h₁ : (Function.support fun g => HahnSeries.mk (fun g' => x.coeff (g, g'))
        (Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g)) = Function.support
        fun g => fun g' => x.coeff (g, g') := by
      simp only [Function.support, ne_eq, mk_eq_zero]
    rw [h₁, Function.support_fun_curry x.coeff]
    exact Set.PartiallyWellOrderedOn.imageProdLex x.isPWO_support'

/-- The equivalence between iterated Hahn series and Hahn series on the lex product. -/
@[simps]
/-
**HahnSeries.iterateEquiv** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：iterateEquiv [PartialOrder Γ'] : R⟦Γ'⟧⟦Γ⟧ ≃ R⟦Γ ×ₗ Γ'⟧ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between iterated Hahn series and Hahn series on the lex product.
-/
def iterateEquiv [PartialOrder Γ'] : R⟦Γ'⟧⟦Γ⟧ ≃ R⟦Γ ×ₗ Γ'⟧ where
  toFun := ofIterate
  invFun := toIterate
  left_inv := congrFun rfl
  right_inv := congrFun rfl

open scoped Classical in
/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
/-
**HahnSeries.single** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：single (a : Γ) : ZeroHom R R⟦Γ⟧ where toFun r
参数：a : Γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`single a r` is the Hahn series which has coefficient `r` at `a` and zero otherw
ise.
-/
def single (a : Γ) : ZeroHom R R⟦Γ⟧ where
  toFun r :=
    { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext (Pi.single_zero _)

variable {a b : Γ} {r : R}

@[simp]
/-
**HahnSeries.coeff_single_same** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_single_same (a : Γ) (r : R) : (single a r).coeff a = r
参数：a : Γ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem coeff_single_same (a : Γ) (r : R) : (single a r).coeff a = r := by
  classical exact Pi.single_eq_same (M := fun _ => R) a r

@[simp]
/-
**HahnSeries.coeff_single_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_single_of_ne (h : b != a) : (single a r).coeff b = 0
参数：h : b != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem coeff_single_of_ne (h : b ≠ a) : (single a r).coeff b = 0 := by
  classical exact Pi.single_eq_of_ne (M := fun _ => R) h r

open scoped Classical in
/-
**HahnSeries.coeff_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_single : (single a r).coeff b = if b = a then r else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem coeff_single : (single a r).coeff b = if b = a then r else 0 := by
  split_ifs with h <;> simp [h]

@[simp]
/-
**HahnSeries.support_single_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_single_of_ne (h : r != 0) : support (single a r) = {a}
参数：h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.support_single_of_ne`：∀ {ι : Type u_1} {M : Type u_3} [inst : Decidab
leEq ι] [inst_1 : Zero M] {i : ι} {a : M},   a ≠ 0 → Function.support (Pi.single
 i a) = {i}
-/
theorem support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} := by
  classical exact Pi.support_single_of_ne h
/-
**HahnSeries.support_single_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_single_subset : support (single a r) subseteq {a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.support_single_subset`：∀ {ι : Type u_1} {M : Type u_3} [inst : Decida
bleEq ι] [inst_1 : Zero M] {i : ι} {a : M},   Function.support (Pi.single i a) ⊆
 {i}
-/
theorem support_single_subset : support (single a r) ⊆ {a} := by
  classical exact Pi.support_single_subset
/-
**HahnSeries.eq_of_mem_support_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：eq_of_mem_support_single {b : Γ} (h : b in support (single a r)) : b = a
参数：h : b in support (single a r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.support_single_subset`：support_single_subset : support (singl
e a r) subseteq {a}
-/
theorem eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
  support_single_subset h
/-
**HahnSeries.single_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_eq_zero : single a (0 : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_
1 : Zero N] (f : ZeroHom M N), f 0 = 0
-/
theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero
/-
**HahnSeries.single_injective** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_injective (a : Γ) : Function.Injective (single a : R -> R⟦Γ⟧)
参数：a : Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
-/
theorem single_injective (a : Γ) : Function.Injective (single a : R → R⟦Γ⟧) :=
  fun r s rs => by rw [← coeff_single_same a r, ← coeff_single_same a s, rs]
/-
**HahnSeries.single_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_ne_zero (h : r != 0) : single a r != 0
参数：h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.single_injective`：single_injective (a : Γ) : Function.Injecti
ve (single a : R -> R⟦Γ⟧)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.single_eq_zero`：single_eq_zero : single a (0 : R) = 0
-/
theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 := fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))

@[simp]
/-
**HahnSeries.single_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `HahnSeries.single_injective`：single_injective (a : Γ) : Function.Injecti
ve (single a : R -> R⟦Γ⟧)
-/
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 :=
  map_eq_zero_iff _ <| single_injective a

@[simp]
/-
**HahnSeries.map_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [inst : PartialOrder Γ] [in
st_1 : Zero R] {a : Γ} {r : R}   [inst_2 : Zero S] (f : ZeroHom R S), ((HahnSeri
es.single a) r).map f = (HahnSeries.single a) (f r)
参数：f : ZeroHom R S；(HahnSeries.single a) r；HahnSeries.single a；f r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.map_coeff`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [in
st : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x : HahnSeries Γ R) 
{F : Type …
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
-/
protected lemma map_single [Zero S] (f : ZeroHom R S) : (single a r).map f = single a (f r) := by
  ext g
  by_cases h : g = a <;> simp [h]
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty Γ] [Nontrivial R] : Nontrivial R⟦Γ⟧ :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine ⟨single default r, single default s, fun con => rs ?_⟩
    rw [← coeff_single_same (default : Γ) r, con, coeff_single_same]⟩

section Order
variable {x : R⟦Γ⟧}

open scoped Classical in
/-- The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero
coefficient if `x ≠ 0`, and is `⊤` when `x = 0`. -/
/-
**HahnSeries.orderTop** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：orderTop (x : R⟦Γ⟧) : WithTop Γ
参数：x : R⟦Γ⟧。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF

--- 原说明 ---
The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` 
has a nonzero
coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
-/
def orderTop (x : R⟦Γ⟧) : WithTop Γ :=
  if h : x = 0 then ⊤ else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
/-
**HahnSeries.orderTop_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
-/
theorem orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤ :=
  dif_pos rfl

@[simp]
/-
**HahnSeries.orderTop_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_of_subsingleton [Subsingleton R] : x.orderTop = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `HahnSeries.instSubsingleton`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Par
tialOrder Γ] [inst_1 : Zero R] [Subsingleton R],   Subsingleton (HahnSeries Γ R)
-/
theorem orderTop_of_subsingleton [Subsingleton R] : x.orderTop = ⊤ :=
  (Subsingleton.eq_zero x) ▸ orderTop_zero
/-
**HahnSeries.orderTop_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_of_ne_zero (hx : x != 0) : orderTop x = x.isWF_support.min (suppo
rt_nonempty_iff.2 hx)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
-/
theorem orderTop_of_ne_zero (hx : x ≠ 0) :
    orderTop x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx
/-
**HahnSeries.orderTop_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} [inst : PartialOrder Γ] [inst_1 : Zero R] 
{x : HahnSeries Γ R}, x.orderTop = ⊤ ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma orderTop_eq_top : orderTop x = ⊤ ↔ x = 0 := by simp [orderTop]
/-
**HahnSeries.orderTop_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} [inst : PartialOrder Γ] [inst_1 : Zero R] 
{x : HahnSeries Γ R}, x.orderTop < ⊤ ↔ x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma orderTop_lt_top : orderTop x < ⊤ ↔ x ≠ 0 := by simp [lt_top_iff_ne_top]
/-
**HahnSeries.orderTop_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `HahnSeries.orderTop_eq_top`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Part
ialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R}, x.orderTop = ⊤ ↔ x = 0
-/
lemma orderTop_ne_top : orderTop x ≠ ⊤ ↔ x ≠ 0 := orderTop_eq_top.not
/-
**HahnSeries.orderTop_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_eq_of_le {x : R⟦Γ⟧} {g : Γ} (hg : g in x.support) (hx : forall g'
 in x.support, g <= g') : orderTop x = g
参数：hg : g in x.support；hx : forall g' in x.support, g <= g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Set.IsWF.min_eq_of_le`：∀ {α : Type u_2} [inst : PartialOrder α] {s : Set
 α} {a : α} (hs : s.IsWF) (ha : a ∈ s), (∀ b ∈ s, a ≤ b) → hs.min ⋯ = a
-/
theorem orderTop_eq_of_le {x : R⟦Γ⟧} {g : Γ} (hg : g ∈ x.support)
    (hx : ∀ g' ∈ x.support, g ≤ g') : orderTop x = g := by
  rw [orderTop_of_ne_zero <| support_nonempty_iff.mp <| Set.nonempty_of_mem hg,
    x.isWF_support.min_eq_of_le hg hx]
/-
**HahnSeries.untop_orderTop_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：untop_orderTop_of_ne_zero {x : R⟦Γ⟧} (hx : x != 0) : WithTop.untop x.order
Top (orderTop_ne_top.2 hx) = x.isWF_support.min (support_nonempty_iff.2 hx)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `WithTop.coe_inj`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
-/
theorem untop_orderTop_of_ne_zero {x : R⟦Γ⟧} (hx : x ≠ 0) :
    WithTop.untop x.orderTop (orderTop_ne_top.2 hx) =
      x.isWF_support.min (support_nonempty_iff.2 hx) :=
  WithTop.coe_inj.mp ((WithTop.coe_untop (orderTop x) (orderTop_ne_top.2 hx)).trans
    (orderTop_of_ne_zero hx))
/-
**HahnSeries.coeff_orderTop_ne** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_orderTop_ne {x : R⟦Γ⟧} {g : Γ} (hg : x.orderTop = g) : x.coeff g != 
0
参数：hg : x.orderTop = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
-/
theorem coeff_orderTop_ne {x : R⟦Γ⟧} {g : Γ} (hg : x.orderTop = g) :
    x.coeff g ≠ 0 := by
  have h : orderTop x ≠ ⊤ := by simp_all only [ne_eq, WithTop.coe_ne_top, not_false_eq_true]
  have hx : x ≠ 0 := orderTop_ne_top.1 h
  rw [orderTop_of_ne_zero hx, WithTop.coe_eq_coe] at hg
  rw [← hg]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)
/-
**HahnSeries.orderTop_ne_of_coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：orderTop_ne_of_coeff_eq_zero {x : R⟦Γ⟧} {i : Γ} (hx : x.coeff i = 0) : x.o
rderTop != i
参数：hx : x.coeff i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.coeff_orderTop_ne`：coeff_orderTop_ne {x : R⟦Γ⟧} {g : Γ} (hg :
 x.orderTop = g) : x.coeff g != 0
-/
theorem orderTop_ne_of_coeff_eq_zero {x : R⟦Γ⟧} {i : Γ} (hx : x.coeff i = 0) :
    x.orderTop ≠ i :=
  fun h ↦ coeff_orderTop_ne h hx
/-
**HahnSeries.orderTop_le_of_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：orderTop_le_of_coeff_ne_zero {Γ} [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x
.coeff g != 0) : x.orderTop <= g
参数：h : x.coeff g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.ne_zero_of_coeff_ne_zero`：ne_zero_of_coeff_ne_zero {x : R⟦Γ⟧}
 {g : Γ} (h : x.coeff g != 0) : x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
-/
theorem orderTop_le_of_coeff_ne_zero {Γ} [LinearOrder Γ] {x : R⟦Γ⟧}
    {g : Γ} (h : x.coeff g ≠ 0) : x.orderTop ≤ g := by
  rw [orderTop_of_ne_zero (ne_zero_of_coeff_ne_zero h), WithTop.coe_le_coe]
  exact Set.IsWF.min_le _ _ ((mem_support _ _).2 h)

@[simp]
/-
**HahnSeries.orderTop_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_single (h : r != 0) : (single a r).orderTop = a
参数：h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.single_ne_zero`：single_ne_zero (h : r != 0) : single a r != 0
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `WithTop.coe_inj`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用定理 `HahnSeries.support_single_subset`：support_single_subset : support (singl
e a r) subseteq {a}
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
-/
theorem orderTop_single (h : r ≠ 0) : (single a r).orderTop = a :=
  (orderTop_of_ne_zero (single_ne_zero h)).trans
    (WithTop.coe_inj.mpr (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h)))))
/-
**HahnSeries.orderTop_single_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_single_le : a <= (single a r).orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `HahnSeries.orderTop_single`：orderTop_single (h : r != 0) : (single a r).
orderTop = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem orderTop_single_le : a ≤ (single a r).orderTop := by
  by_cases hr : r = 0
  · simp only [hr, map_zero, orderTop_zero, le_top]
  · rw [orderTop_single hr]
/-
**HahnSeries.lt_orderTop_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：lt_orderTop_single {g g' : Γ} (hgg' : g < g') : g < (single g' r).orderTop
参数：hgg' : g < g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用定理 `HahnSeries.orderTop_single_le`：orderTop_single_le : a <= (single a r).or
derTop
-/
theorem lt_orderTop_single {g g' : Γ} (hgg' : g < g') : g < (single g' r).orderTop :=
  lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le
/-
**HahnSeries.coeff_eq_zero_of_lt_orderTop** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：coeff_eq_zero_of_lt_orderTop {x : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.
coeff i = 0
参数：hi : i < x.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `HahnSeries.coeff_zero`：coeff_zero {a : Γ} : (0 : R⟦Γ⟧).coeff a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用定理 `Set.IsWF.not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a
 : α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → ¬a < hs.min hn
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
-/
theorem coeff_eq_zero_of_lt_orderTop {x : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · exact coeff_zero
  contrapose! hi
  rw [← mem_support] at hi
  rw [orderTop_of_ne_zero hx, WithTop.coe_lt_coe]
  exact Set.IsWF.not_lt_min _ _ hi

/-- A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or
zero if the series vanishes. -/
/-
**HahnSeries.leadingCoeff** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff (x : R⟦Γ⟧) : R
参数：x : R⟦Γ⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A leading coefficient of a Hahn series is the coefficient of a lowest-order nonz
ero term, or
zero if the series vanishes.
-/
def leadingCoeff (x : R⟦Γ⟧) : R := x.orderTop.recTopCoe 0 x.coeff

@[simp]
/-
**HahnSeries.leadingCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧) = 0 := by simp [leadingCoeff]
/-
**HahnSeries.leadingCoeff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (hx : x != 0) : x.leadingCoeff = x.coef
f (x.orderTop.untop <| orderTop_ne_top.2 hx)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `WithTop.untop.congr_simp`：∀ {α : Type u_1} (x x_1 : WithTop α) (e_x : x 
= x_1) (a : x ≠ ⊤), x.untop a = x_1.untop ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (hx : x ≠ 0) :
    x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 hx) := by
  simp [leadingCoeff, orderTop, hx]

@[simp]
/-
**HahnSeries.leadingCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_eq_zero {x : R⟦Γ⟧} : x.leadingCoeff = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
-/
theorem leadingCoeff_eq_zero {x : R⟦Γ⟧} : x.leadingCoeff = 0 ↔ x = 0 := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, coeff_orderTop_ne, *]
/-
**HahnSeries.leadingCoeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_ne_zero {x : R⟦Γ⟧} : x.leadingCoeff != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `HahnSeries.leadingCoeff_eq_zero`：leadingCoeff_eq_zero {x : R⟦Γ⟧} : x.lea
dingCoeff = 0 ↔ x = 0
-/
theorem leadingCoeff_ne_zero {x : R⟦Γ⟧} : x.leadingCoeff ≠ 0 ↔ x ≠ 0 :=
  leadingCoeff_eq_zero.not

@[simp]
/-
**HahnSeries.leadingCoeff_of_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_of_single {a : Γ} {r : R} : leadingCoeff (single a r) = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.orderTop_single`：orderTop_single (h : r != 0) : (single a r).
orderTop = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
-/
theorem leadingCoeff_of_single {a : Γ} {r : R} : leadingCoeff (single a r) = r := by
  by_cases h : r = 0 <;> simp [leadingCoeff, h]
/-
**HahnSeries.coeff_untop_eq_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_untop_eq_leadingCoeff {x : R⟦Γ⟧} (hx) : x.coeff (x.orderTop.untop hx
) = x.leadingCoeff
参数：hx。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `WithTop.untop_eq_iff`：∀ {α : Type u_1} {a : WithTop α} {b : α} (h : a ≠ 
⊤), a.untop h = b ↔ a = ↑b
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
-/
theorem coeff_untop_eq_leadingCoeff {x : R⟦Γ⟧} (hx) :
    x.coeff (x.orderTop.untop hx) = x.leadingCoeff := by
  rw [orderTop_ne_top] at hx
  rw [leadingCoeff_of_ne_zero hx, (WithTop.untop_eq_iff _).mpr (orderTop_of_ne_zero hx)]

variable [Zero Γ]

open scoped Classical in
/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
  nonzero coefficient, the order of 0 is 0. -/
/-
**HahnSeries.order** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：order (x : R⟦Γ⟧) : Γ
参数：x : R⟦Γ⟧。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF

--- 原说明 ---
The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has
 a
  nonzero coefficient, the order of 0 is 0.
-/
def order (x : R⟦Γ⟧) : Γ :=
  if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
/-
**HahnSeries.order_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_zero : order (0 : R⟦Γ⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
-/
theorem order_zero : order (0 : R⟦Γ⟧) = 0 :=
  dif_pos rfl
/-
**HahnSeries.order_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x = x.isWF_support.min (suppo
rt_nonempty_iff.2 hx)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
-/
theorem order_of_ne {x : R⟦Γ⟧} (hx : x ≠ 0) :
    order x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx
/-
**HahnSeries.order_eq_orderTop_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：order_eq_orderTop_of_ne_zero (hx : x != 0) : order x = orderTop x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
-/
theorem order_eq_orderTop_of_ne_zero (hx : x ≠ 0) : order x = orderTop x := by
  rw [order_of_ne hx, orderTop_of_ne_zero hx]

@[simp]
/-
**HahnSeries.coeff_order_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_order_eq_zero {x : R⟦Γ⟧} : x.coeff x.order = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_order_eq_zero {x : R⟦Γ⟧} : x.coeff x.order = 0 ↔ x = 0 := by
  refine ⟨not_imp_not.1 fun hx ↦ ?_, by simp +contextual⟩
  rw [order_of_ne hx]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)
/-
**HahnSeries.order_le_of_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_le_of_coeff_ne_zero {Γ} [Zero Γ] [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} 
(h : x.coeff g != 0) : x.order <= g
参数：h : x.coeff g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.ne_zero_of_coeff_ne_zero`：ne_zero_of_coeff_ne_zero {x : R⟦Γ⟧}
 {g : Γ} (h : x.coeff g != 0) : x != 0
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
-/
theorem order_le_of_coeff_ne_zero {Γ} [Zero Γ] [LinearOrder Γ] {x : R⟦Γ⟧}
    {g : Γ} (h : x.coeff g ≠ 0) : x.order ≤ g :=
  le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWF.min_le _ _ ((mem_support _ _).2 h))

@[simp]
/-
**HahnSeries.order_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_single (h : r != 0) : (single a r).order = a
参数：h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.single_ne_zero`：single_ne_zero (h : r != 0) : single a r != 0
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `HahnSeries.support_single_subset`：support_single_subset : support (singl
e a r) subseteq {a}
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
-/
theorem order_single (h : r ≠ 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))
/-
**HahnSeries.coeff_eq_zero_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_eq_zero_of_lt_order {x : R⟦Γ⟧} {i : Γ} (hi : i < x.order) : x.coeff 
i = 0
参数：hi : i < x.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Set.IsWF.not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a
 : α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → ¬a < hs.min hn
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
-/
theorem coeff_eq_zero_of_lt_order {x : R⟦Γ⟧} {i : Γ} (hi : i < x.order) : x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi
/-
**HahnSeries.zero_lt_orderTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：zero_lt_orderTop_iff {x : R⟦Γ⟧} (hx : x != 0) : 0 < x.orderTop ↔ 0 < x.ord
er
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem zero_lt_orderTop_iff {x : R⟦Γ⟧} (hx : x ≠ 0) :
    0 < x.orderTop ↔ 0 < x.order := by
  simp_all [orderTop_of_ne_zero hx, order_of_ne hx]
/-
**HahnSeries.zero_lt_orderTop_of_order** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：zero_lt_orderTop_of_order {x : R⟦Γ⟧} (hx : 0 < x.order) : 0 < x.orderTop
参数：hx : 0 < x.order。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.zero_lt_orderTop_iff`：zero_lt_orderTop_iff {x : R⟦Γ⟧} (hx : x
 != 0) : 0 < x.orderTop ↔ 0 < x.order
-/
theorem zero_lt_orderTop_of_order {x : R⟦Γ⟧} (hx : 0 < x.order) : 0 < x.orderTop := by
  by_cases h : x = 0
  · simp_all only [order_zero, lt_self_iff_false]
  · exact (zero_lt_orderTop_iff h).mpr hx
/-
**HahnSeries.zero_le_orderTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：zero_le_orderTop_iff {x : R⟦Γ⟧} : 0 <= x.orderTop ↔ 0 <= x.order
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
-/
theorem zero_le_orderTop_iff {x : R⟦Γ⟧} : 0 ≤ x.orderTop ↔ 0 ≤ x.order := by
  by_cases h : x = 0
  · simp_all
  · simp_all [order_of_ne h, orderTop_of_ne_zero h]
/-
**HahnSeries.leadingCoeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_eq {x : R⟦Γ⟧} : x.leadingCoeff = x.coeff x.order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `HahnSeries.coeff_zero`：coeff_zero {a : Γ} : (0 : R⟦Γ⟧).coeff a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `WithTop.untop.congr_simp`：∀ {α : Type u_1} (x x_1 : WithTop α) (e_x : x 
= x_1) (a : x ≠ ⊤), x.untop a = x_1.untop ⋯
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_eq {x : R⟦Γ⟧} : x.leadingCoeff = x.coeff x.order := by
  by_cases h : x = 0
  · rw [h, leadingCoeff_zero, coeff_zero]
  · simp [leadingCoeff_of_ne_zero, orderTop_of_ne_zero, order_of_ne, h]

end Order

section Finsupp

/-- Create a `HahnSeries` with a `Finsupp` as coefficients. -/
/-
**HahnSeries.ofFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：ofFinsupp : ZeroHom (Γ ->₀ R) R⟦Γ⟧ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `HahnSeries` with a `Finsupp` as coefficients.
-/
def ofFinsupp : ZeroHom (Γ →₀ R) R⟦Γ⟧ where
  toFun f := { coeff := f, isPWO_support' := f.hasFiniteSupport.isPWO }
  map_zero' := by simp

@[simp]
/-
**HahnSeries.coeff_ofFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_ofFinsupp (f : Γ ->₀ R) (a : Γ) : (ofFinsupp f).coeff a = f a
参数：f : Γ ->₀ R；a : Γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_ofFinsupp (f : Γ →₀ R) (a : Γ) : (ofFinsupp f).coeff a = f a := rfl

end Finsupp

section Domain

variable [PartialOrder Γ']

open scoped Classical in
/-- Extends the domain of a `HahnSeries` by an `OrderEmbedding`. -/
/-
**HahnSeries.embDomain** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：embDomain (f : Γ ↪o Γ') : R⟦Γ⟧ -> R⟦Γ'⟧
参数：f : Γ ↪o Γ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extends the domain of a `HahnSeries` by an `OrderEmbedding`.
-/
def embDomain (f : Γ ↪o Γ') : R⟦Γ⟧ → R⟦Γ'⟧ := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose hb
        rw [Function.mem_support, dif_neg hb, Classical.not_not] }

@[simp]
/-
**HahnSeries.embDomain_coeff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a : Γ} : (embDomain f x).coeff (
f a) = x.coeff a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.embDomain.eq_1`：∀ {Γ : Type u_1} {Γ' : Type u_2} {R : Type u_
3} [inst : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : PartialOrder Γ']   (f : Γ
 ↪o Γ') (x : Ha…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
-/
theorem embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a : Γ} :
    (embDomain f x).coeff (f a) = x.coeff a := by
  rw [embDomain]
  dsimp only
  by_cases ha : a ∈ x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose ha
    obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha
    rwa [f.injective hb2] at hb1

@[simp]
/-
**HahnSeries.embDomain_mk_coeff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_mk_coeff {f : Γ -> Γ'} (hfi : Function.Injective f) (hf : forall
 g g' : Γ, f g <= f g' ↔ g <= g') {x : R⟦Γ⟧} {a : Γ} : (embDomain ⟨⟨f, hfi⟩, hf 
_ _⟩ x).coeff (f a) = x.coeff a
参数：hfi : Function.Injective f；hf : forall g g' : Γ, f g <= f g' ↔ g <= g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
-/
theorem embDomain_mk_coeff {f : Γ → Γ'} (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') {x : R⟦Γ⟧} {a : Γ} :
    (embDomain ⟨⟨f, hfi⟩, hf _ _⟩ x).coeff (f a) = x.coeff a :=
  embDomain_coeff
/-
**HahnSeries.embDomain_notin_image_support** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries
`。
形式化陈述：embDomain_notin_image_support {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ 
f '' x.support) : (embDomain f x).coeff b = 0
参数：hb : b ∉ f '' x.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem embDomain_notin_image_support {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'}
    (hb : b ∉ f '' x.support) : (embDomain f x).coeff b = 0 :=
  dif_neg hb
/-
**HahnSeries.support_embDomain_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_embDomain_subset {f : Γ ↪o Γ'} {x : R⟦Γ⟧} : support (embDomain f x
) subseteq f '' x.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
· 使用定理 `HahnSeries.embDomain_notin_image_support`：embDomain_notin_image_support 
{f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ f '' x.support) : (embDomain f x).co
eff b = 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem support_embDomain_subset {f : Γ ↪o Γ'} {x : R⟦Γ⟧} :
    support (embDomain f x) ⊆ f '' x.support := by
  intro g hg
  contrapose hg
  rw [mem_support, embDomain_notin_image_support hg, Classical.not_not]
/-
**HahnSeries.embDomain_of_notMem_range** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_of_notMem_range {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.
range f) : (embDomain f x).coeff b = 0
参数：hb : b ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.embDomain_notin_image_support`：embDomain_notin_image_support 
{f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ f '' x.support) : (embDomain f x).co
eff b = 0
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem embDomain_of_notMem_range {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

@[simp]
/-
**HahnSeries.embDomain_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : R⟦Γ⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.embDomain_notin_image_support`：embDomain_notin_image_support 
{f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ f '' x.support) : (embDomain f x).co
eff b = 0
· 使用定理 `HahnSeries.support_zero`：support_zero : support (0 : R⟦Γ⟧) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : R⟦Γ⟧) = 0 := by
  ext
  simp [embDomain_notin_image_support]

@[simp]
/-
**HahnSeries.embDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} : embDomain f (single g r) 
= single (f g) r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.embDomain_notin_image_support`：embDomain_notin_image_support 
{f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ f '' x.support) : (embDomain f x).co
eff b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `HahnSeries.support_zero`：support_zero : support (0 : R⟦Γ⟧) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.support_single_of_ne`：support_single_of_ne (h : r != 0) : sup
port (single a r) = {a}
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
-/
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r := by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support, coeff_single_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]
/-
**HahnSeries.embDomain_injective** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_injective {f : Γ ↪o Γ'} : Function.Injective (embDomain f : R⟦Γ⟧
 -> R⟦Γ'⟧)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `HahnSeries.ext_iff`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder
 Γ} {inst_1 : Zero R} {x y : HahnSeries Γ R},   x = y ↔ x.coeff = y.coeff
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
-/
theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : R⟦Γ⟧ → R⟦Γ'⟧) := fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff, funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg

@[simp]
/-
**HahnSeries.orderTop_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_embDomain {Γ : Type*} [LinearOrder Γ] {f : Γ ↪o Γ'} {x : R⟦Γ⟧} : 
(embDomain f x).orderTop = WithTop.map f x.orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.embDomain_zero`：embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0
 : R⟦Γ⟧) = 0
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `WithTop.map_coe`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (a : α), Wi
thTop.map f ↑a = ↑(f a)
· 使用定理 `HahnSeries.orderTop_eq_of_le`：orderTop_eq_of_le {x : R⟦Γ⟧} {g : Γ} (hg :
 g in x.support) (hx : forall g' in x.support, g <= g') : orderTop x = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
· 使用定理 `HahnSeries.coeff_orderTop_ne`：coeff_orderTop_ne {x : R⟦Γ⟧} {g : Γ} (hg :
 x.orderTop = g) : x.coeff g != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `HahnSeries.support_embDomain_subset`：support_embDomain_subset {f : Γ ↪o 
Γ'} {x : R⟦Γ⟧} : support (embDomain f x) subseteq f '' x.support
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `WithTop.untop_le_iff`：∀ {α : Type u_1} {a : α} [inst : LE α] {x : WithTo
p α} (hx : x ≠ ⊤), x.untop hx ≤ a ↔ x ≤ ↑a
· 使用定理 `HahnSeries.orderTop_le_of_coeff_ne_zero`：orderTop_le_of_coeff_ne_zero {Γ
} [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.orderTop <= g
-/
theorem orderTop_embDomain {Γ : Type*} [LinearOrder Γ] {f : Γ ↪o Γ'} {x : R⟦Γ⟧} :
    (embDomain f x).orderTop = WithTop.map f x.orderTop := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  rw [← WithTop.coe_untop x.orderTop (by simpa using hx), WithTop.map_coe]
  apply orderTop_eq_of_le
  · simpa using coeff_orderTop_ne (by simp)
  intro y hy
  obtain ⟨z, hz, rfl⟩ :=
    (Set.mem_image _ _ _).mp <| Set.mem_of_subset_of_mem support_embDomain_subset hy
  rw [OrderEmbedding.le_iff_le, WithTop.untop_le_iff]
  apply orderTop_le_of_coeff_ne_zero
  simpa using hz

end Domain

end Zero

section LinearOrder

variable [Zero R] [LinearOrder Γ]

@[deprecated "directly use n as a lower bound." (since := "2026-01-02")]
/-
**HahnSeries.forallLTEqZero_supp_BddBelow** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：forallLTEqZero_supp_BddBelow (f : Γ -> R) (n : Γ) (hn : forall (m : Γ), m 
< n -> f m = 0) : BddBelow (Function.support f)
参数：f : Γ -> R；n : Γ；hn : forall (m : Γ), m < n -> f m = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem forallLTEqZero_supp_BddBelow (f : Γ → R) (n : Γ) (hn : ∀ (m : Γ), m < n → f m = 0) :
    BddBelow (Function.support f) := by
  refine ⟨n, fun _ ↦ ?_⟩
  contrapose
  simp_all

@[deprecated bddBelow_empty (since := "2026-01-02")]
/-
**HahnSeries.BddBelow_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：BddBelow_zero [Nonempty Γ] : BddBelow (Function.support (0 : Γ -> R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.support_zero`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M], 
Function.support 0 = ∅
-/
theorem BddBelow_zero [Nonempty Γ] : BddBelow (Function.support (0 : Γ → R)) := by
  simp
/-
**HahnSeries.le_orderTop_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：le_orderTop_iff_forall {x : R⟦Γ⟧} {i : WithTop Γ} : i <= x.orderTop ↔ fora
ll j : Γ, j < i -> x.coeff j = 0 where mp hi j hj
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_orderTop`：coeff_eq_zero_of_lt_orderTop {x
 : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.coeff i = 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
-/
theorem le_orderTop_iff_forall {x : R⟦Γ⟧} {i : WithTop Γ} :
    i ≤ x.orderTop ↔ ∀ j : Γ, j < i → x.coeff j = 0 where
  mp hi j hj := coeff_eq_zero_of_lt_orderTop (hj.trans_le hi)
  mpr H := by
    obtain rfl | h := eq_or_ne x 0
    · simp
    · by_contra! hi
      exact x.isWF_support.min_mem (support_nonempty_iff.2 h) (H _ (orderTop_of_ne_zero h ▸ hi))
/-
**HahnSeries.orderTop_lt_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_lt_iff_exists {x : R⟦Γ⟧} {i : WithTop Γ} : x.orderTop < i ↔ exist
s j : Γ, j < i ∧ x.coeff j != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `HahnSeries.le_orderTop_iff_forall`：le_orderTop_iff_forall {x : R⟦Γ⟧} {i 
: WithTop Γ} : i <= x.orderTop ↔ forall j : Γ, j < i -> x.coeff j = 0 where mp h
i j hj
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem orderTop_lt_iff_exists {x : R⟦Γ⟧} {i : WithTop Γ} :
    x.orderTop < i ↔ ∃ j : Γ, j < i ∧ x.coeff j ≠ 0 := by
  rw [← not_le, le_orderTop_iff_forall]
  simp
/-
**HahnSeries.le_order_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：le_order_iff_forall [Zero Γ] {x : R⟦Γ⟧} {i : Γ} (h : x != 0) : i <= x.orde
r ↔ forall j < i, x.coeff j = 0 where mp hi j hj
参数：h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_order`：coeff_eq_zero_of_lt_order {x : R⟦Γ
⟧} {i : Γ} (hi : i < x.order) : x.coeff i = 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_order_eq_zero`：coeff_order_eq_zero {x : R⟦Γ⟧} : x.coeff
 x.order = 0 ↔ x = 0
-/
theorem le_order_iff_forall [Zero Γ] {x : R⟦Γ⟧} {i : Γ} (h : x ≠ 0) :
    i ≤ x.order ↔ ∀ j < i, x.coeff j = 0 where
  mp hi j hj := coeff_eq_zero_of_lt_order (hj.trans_le hi)
  mpr H := by
    contrapose! h
    have := H _ h
    rwa [coeff_order_eq_zero] at this
/-
**HahnSeries.order_lt_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_lt_iff_exists [Zero Γ] {x : R⟦Γ⟧} {i : Γ} (h : x != 0) : x.order < i
 ↔ exists j < i, x.coeff j != 0
参数：h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `HahnSeries.le_order_iff_forall`：le_order_iff_forall [Zero Γ] {x : R⟦Γ⟧} 
{i : Γ} (h : x != 0) : i <= x.order ↔ forall j < i, x.coeff j = 0 where mp hi j 
hj
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem order_lt_iff_exists [Zero Γ] {x : R⟦Γ⟧} {i : Γ} (h : x ≠ 0) :
    x.order < i ↔ ∃ j < i, x.coeff j ≠ 0 := by
  rw [← not_le, le_order_iff_forall h]
  simp

variable [LocallyFiniteOrder Γ]

@[deprecated BddBelow.isWF (since := "2026-01-02")]
/-
**HahnSeries.suppBddBelow_supp_PWO** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：suppBddBelow_supp_PWO (f : Γ -> R) (hf : BddBelow (Function.support f)) : 
(Function.support f).IsPWO
参数：f : Γ -> R；hf : BddBelow (Function.support f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsWF.isPWO`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}, s.I
sWF → s.IsPWO
· 使用定理 `BddBelow.isWF`：BddBelow.isWF : BddBelow s -> IsWF s
-/
theorem suppBddBelow_supp_PWO (f : Γ → R) (hf : BddBelow (Function.support f)) :
    (Function.support f).IsPWO :=
  hf.isWF.isPWO

/-- Construct a Hahn series from any function whose support is bounded below. -/
@[simps]
/-
**HahnSeries.ofSuppBddBelow** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：ofSuppBddBelow (f : Γ -> R) (hf : BddBelow (Function.support f)) : R⟦Γ⟧
参数：f : Γ -> R；hf : BddBelow (Function.support f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a Hahn series from any function whose support is bounded below.
-/
def ofSuppBddBelow (f : Γ → R) (hf : BddBelow (Function.support f)) : R⟦Γ⟧ :=
  ⟨f, hf.isWF.isPWO⟩

@[simp]
/-
**HahnSeries.ofSuppBddBelow_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ofSuppBddBelow_zero [Nonempty Γ] : ofSuppBddBelow 0 (by simp) = (0 : R⟦Γ⟧)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSuppBddBelow_zero [Nonempty Γ] : ofSuppBddBelow 0 (by simp) = (0 : R⟦Γ⟧) :=
  rfl

@[deprecated (since := "2026-01-02")]
alias zero_ofSuppBddBelow := ofSuppBddBelow_zero

@[simp]
/-
**HahnSeries.ofSuppBddBelow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ofSuppBddBelow_eq_zero {f : Γ -> R} {hf} : ofSuppBddBelow f hf = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext_iff`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder
 Γ} {inst_1 : Zero R} {x y : HahnSeries Γ R},   x = y ↔ x.coeff = y.coeff
-/
theorem ofSuppBddBelow_eq_zero {f : Γ → R} {hf} : ofSuppBddBelow f hf = 0 ↔ f = 0 :=
  HahnSeries.ext_iff

@[simp]
/-
**HahnSeries.coeff_ofSuppBddBelow** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_ofSuppBddBelow {f : Γ -> R} {hf} : (ofSuppBddBelow f hf).coeff = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_ofSuppBddBelow {f : Γ → R} {hf} : (ofSuppBddBelow f hf).coeff = f :=
  rfl

@[deprecated le_order_iff_forall (since := "2026-01-02")]
/-
**HahnSeries.order_ofForallLtEqZero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_ofForallLtEqZero [Zero Γ] (f : Γ -> R) (hf : f != 0) (n : Γ) (hn : f
orall (m : Γ), m < n -> f m = 0) : n <= order (ofSuppBddBelow f (forallLTEqZero_
supp_BddBelow f n hn))
参数：f : Γ -> R；hf : f != 0；n : Γ；hn : forall (m : Γ), m < n -> f m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.forallLTEqZero_supp_BddBelow`：forallLTEqZero_supp_BddBelow (f
 : Γ -> R) (n : Γ) (hn : forall (m : Γ), m < n -> f m = 0) : BddBelow (Function.
support f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.le_order_iff_forall`：le_order_iff_forall [Zero Γ] {x : R⟦Γ⟧} 
{i : Γ} (h : x != 0) : i <= x.order ↔ forall j < i, x.coeff j = 0 where mp hi j 
hj
-/
theorem order_ofForallLtEqZero [Zero Γ] (f : Γ → R) (hf : f ≠ 0) (n : Γ)
    (hn : ∀ (m : Γ), m < n → f m = 0) :
    n ≤ order (ofSuppBddBelow f (forallLTEqZero_supp_BddBelow f n hn)) := by
  rw [le_order_iff_forall]
  · exact hn
  · simpa

end LinearOrder

section Truncate
variable [Zero R]

/-- Zeroes out coefficients of a `HahnSeries` at indices not less than `c`. -/
/-
**HahnSeries.truncLT** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：truncLT [PartialOrder Γ] [DecidableLT Γ] (c : Γ) : ZeroHom R⟦Γ⟧ R⟦Γ⟧ where
 toFun x
参数：c : Γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Zeroes out coefficients of a `HahnSeries` at indices not less than `c`.
-/
def truncLT [PartialOrder Γ] [DecidableLT Γ] (c : Γ) : ZeroHom R⟦Γ⟧ R⟦Γ⟧ where
  toFun x :=
    { coeff i := if i < c then x.coeff i else 0
      isPWO_support' := Set.IsPWO.mono x.isPWO_support (by simp) }
  map_zero' := by ext; simp
/-
**HahnSeries.support_truncLT** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_truncLT [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) : (tru
ncLT c x).support = {y in x.support | y < c}
参数：c : Γ；x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_truncLT [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) :
    (truncLT c x).support = {y ∈ x.support | y < c} := by
  simp [truncLT, Function.support, and_comm]
/-
**HahnSeries.support_truncLT_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_truncLT_subset [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧)
 : (truncLT c x).support subseteq x.support
参数：c : Γ；x : R⟦Γ⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.support_truncLT`：support_truncLT [PartialOrder Γ] [DecidableL
T Γ] (c : Γ) (x : R⟦Γ⟧) : (truncLT c x).support = {y in x.support | y < c}
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s
-/
theorem support_truncLT_subset [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) :
    (truncLT c x).support ⊆ x.support := by
  rw [support_truncLT]
  exact Set.sep_subset ..

@[simp]
/-
**HahnSeries.coeff_truncLT** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} [inst : Zero R] [inst_1 : PartialOrder Γ] 
[inst_2 : DecidableLT Γ] (c : Γ)   (x : HahnSeries Γ R) (i : Γ), ((HahnSeries.tr
uncLT c) x).coeff i = if i < c then x.coeff i else 0
参数：c : Γ；x : HahnSeries Γ R；i : Γ；(HahnSeries.truncLT c) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coeff_truncLT [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) (i : Γ) :
    (truncLT c x).coeff i = if i < c then x.coeff i else 0 := rfl
/-
**HahnSeries.coeff_truncLT_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_truncLT_of_lt [PartialOrder Γ] [DecidableLT Γ] {c i : Γ} (h : i < c)
 (x : R⟦Γ⟧) : (truncLT c x).coeff i = x.coeff i
参数：h : i < c；x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_truncLT_of_lt [PartialOrder Γ] [DecidableLT Γ] {c i : Γ} (h : i < c) (x : R⟦Γ⟧) :
    (truncLT c x).coeff i = x.coeff i := by
  simp [h]
/-
**HahnSeries.coeff_truncLT_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_truncLT_of_le [LinearOrder Γ] {c i : Γ} (h : c <= i) (x : R⟦Γ⟧) : (t
runcLT c x).coeff i = 0
参数：h : c <= i；x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem coeff_truncLT_of_le [LinearOrder Γ] {c i : Γ} (h : c ≤ i) (x : R⟦Γ⟧) :
    (truncLT c x).coeff i = 0 := by
  simp [h]

end Truncate

end HahnSeries

