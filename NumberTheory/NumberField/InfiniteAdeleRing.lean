/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# The infinite adele ring of a number field

This file contains the formalisation of the infinite adele ring of a number field as the
finite product of completions over its infinite places.

## Main definitions

- `NumberField.InfiniteAdeleRing` of a number field `K` is defined as the product of
  the completions of `K` over its infinite places.
- `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` is the ring isomorphism between
  the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of `K`.

## Main results
- `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
  locally compact space.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

@[expose] public section

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The infinite adele ring

The infinite adele ring is the finite product of completions of a number field over its
infinite places. See `NumberField.InfinitePlace` for the definition of an infinite place and
`NumberField.InfinitePlace.Completion` for the associated completion.
-/

/-- The infinite adele ring of a number field. -/
/-
**NumberField.InfiniteAdeleRing** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：InfiniteAdeleRing (K : Type*) [Field K]
参数：K : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infinite adele ring of a number field.
-/
def InfiniteAdeleRing (K : Type*) [Field K] := (v : InfinitePlace K) → v.Completion
deriving CommRing, Inhabited, TopologicalSpace, IsTopologicalRing, Algebra K

namespace InfiniteAdeleRing

/-- `K∞` is notation for `NumberField.InfiniteAdeleRing K`. -/
scoped[NumberField.AdeleRing] notation:max K "∞" => InfiniteAdeleRing K

open scoped AdeleRing

variable (K : Type*) [Field K]

/-
**NumberField.InfiniteAdeleRing.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Infinite
AdeleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NumberField K] : Nontrivial K∞ :=
  (inferInstance : Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w
/-
**NumberField.InfiniteAdeleRing.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.InfiniteAdeleRing`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] (x : K) (v : NumberField.InfinitePlace K
),   (algebraMap K (NumberField.InfiniteAdeleRing K)) x v = { toCompletion := ↑(
WithAbs.toAbs (↑v) x) }
参数：K : Type u_1；x : K；v : NumberField.InfinitePlace K；algebraMap K (NumberField.
InfiniteAdeleRing K)；WithAbs.toAbs (↑v) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem algebraMap_apply (x : K) (v : InfinitePlace K) : algebraMap K K∞ x v = x := rfl

/-- The infinite adele ring is locally compact. -/
/-
**NumberField.InfiniteAdeleRing.locallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `N
umberField.InfiniteAdeleRing`。
形式化陈述：locallyCompactSpace [NumberField K] : LocallyCompactSpace K∞
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The infinite adele ring is locally compact.
-/
instance locallyCompactSpace [NumberField K] : LocallyCompactSpace K∞ :=
  Pi.locallyCompactSpace_of_finite

open scoped Classical in
/-- The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field. -/
/-
**NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace** 是 Mathlib 中的一个缩写定义，位于命名空间
 `NumberField.InfiniteAdeleRing`。
形式化陈述：ringEquiv_mixedSpace : K∞ ≃+* mixedEmbedding.mixedSpace K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w

--- 原说明 ---
The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field.
-/
abbrev ringEquiv_mixedSpace : K∞ ≃+* mixedEmbedding.mixedSpace K :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.Completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquivRealOfIsReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.ringEquivComplexOfIsComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => ℂ) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

@[simp]
/-
**NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.InfiniteAdeleRing`。
形式化陈述：ringEquiv_mixedSpace_apply (x : K∞) : ringEquiv_mixedSpace K x = (fun (v :
 {w : InfinitePlace K // IsReal w}) => extensionEmbeddingOfIsReal v.2 (x v), fun
 (v : {w : InfinitePlace K // IsComplex w}) => extensionEmbedding v.1 (x v))
参数：x : K∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ringEquiv_mixedSpace_apply (x : K∞) :
    ringEquiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) => extensionEmbeddingOfIsReal v.2 (x v),
       fun (v : {w : InfinitePlace K // IsComplex w}) => extensionEmbedding v.1 (x v)) := rfl

/-- Transfers the embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`. -/
/-
**NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.InfiniteAdeleRing`。
形式化陈述：mixedEmbedding_eq_algebraMap_comp {x : K} : mixedEmbedding K x = ringEquiv
_mixedSpace K (algebraMap K K∞ x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.mixedEmbedding_apply_isReal`：mixedEmbedding_a
pply_isReal (x : K) (w : {w // IsReal w}) : (mixedEmbedding K x).1 w = embedding
_of_isReal w.prop x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe`：ext
ensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : WithAbs v
.1) : extensionEmbeddingOfIsReal hv x = embedding_of_isRe…
· 使用定理 `WithAbs.equiv_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (self
 : WithAb…
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbedding_coe`：extensionEm
bedding_coe (x : WithAbs v.1) : extensionEmbedding v x = v.embedding (WithAbs.eq
uiv v.1 x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex`：mixedEmbeddin
g_apply_isComplex (x : K) (w : {w // IsComplex w}) : (mixedEmbedding K x).2 w = 
w.val.embedding x

--- 原说明 ---
Transfers the embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite 
adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r
₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`.
-/
theorem mixedEmbedding_eq_algebraMap_comp {x : K} :
    mixedEmbedding K x = ringEquiv_mixedSpace K (algebraMap K K∞ x) := by
  ext v <;> simp

/--
*Weak approximation for the infinite adele ring*

The number field $K$ is dense in the infinite adele ring $\prod_v K_v$.
-/
/-
**NumberField.InfiniteAdeleRing.denseRange_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfiniteAdeleRing`。
形式化陈述：denseRange_algebraMap [NumberField K] : DenseRange algebraMap K K∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.comp`：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRa
nge g) (hf : DenseRange f) (cg : Continuous g) : DenseRange (g ∘ f)
· 使用定理 `DenseRange.piMap`：DenseRange.piMap {ι : Type*} {X Y : ι -> Type*} [foral
l i, TopologicalSpace (Y i)] {f : (i : ι) -> (X i) -> (Y i)} (hf : forall i, Den
seRang…
· 使用定理 `NumberField.InfinitePlace.Completion.denseRange_coe`：denseRange_coe : De
nseRange ((↑) : WithAbs v.1 -> v.Completion)
· 使用定理 `NumberField.InfinitePlace.denseRange_algebraMap_pi`：∀ (K : Type u_1) [in
st : Field K] [NumberField K],   DenseRange ⇑(algebraMap K ((v : NumberField.Inf
initePlace K) → WithAbs ↑v))
· 使用定理 `Continuous.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7}
 [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B 
i)] {f…
· 使用定理 `NumberField.InfinitePlace.Completion.continuous_coe`：continuous_coe : Co
ntinuous ((↑) : WithAbs v.1 -> v.Completion)

--- 原说明 ---
*Weak approximation for the infinite adele ring*

The number field $K$ is dense in the infinite adele ring $\prod_v K_v$.
-/
theorem denseRange_algebraMap [NumberField K] : DenseRange <| algebraMap K K∞ :=
  (DenseRange.piMap fun v => Completion.denseRange_coe v).comp
    (InfinitePlace.denseRange_algebraMap_pi K) (.piMap fun v => Completion.continuous_coe v)

/-- The norm on the infinite adele ring is given by the product of the normalized norms
across infinite places. The normalized norm is the real norm at real places and the
square of the complex norm at complex places. -/
/-
**NumberField.InfiniteAdeleRing.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Infinite
AdeleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm on the infinite adele ring is given by the product of the normalized no
rms
across infinite places. The normalized norm is the real norm at real places and 
the
square of the complex norm at complex places.
-/
instance [NumberField K] : Norm K∞ where norm x := ∏ v, ‖x v‖ ^ v.mult

variable {K}
/-
**NumberField.InfiniteAdeleRing.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
InfiniteAdeleRing`。
形式化陈述：norm_def [NumberField K] (x : K∞) : ‖x‖ = ∏ v, ‖x v‖ ^ v.mult
参数：x : K∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def [NumberField K] (x : K∞) : ‖x‖ = ∏ v, ‖x v‖ ^ v.mult := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**NumberField.InfiniteAdeleRing.norm_eq_zero_of_not_isUnit** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.InfiniteAdeleRing`。
形式化陈述：norm_eq_zero_of_not_isUnit [NumberField K] {x : K∞} (hx : ¬IsUnit x) : ‖x‖
 = 0
参数：hx : ¬IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用引理 `Pi.isUnit_iff`：Pi.isUnit_iff : IsUnit x ↔ forall i, IsUnit (x i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_eq_zero_iff`：prod_eq_zero_iff : ∏ x in s, f x = 0 ↔ exists a
 in s, f a = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem norm_eq_zero_of_not_isUnit [NumberField K] {x : K∞} (hx : ¬IsUnit x) :
    ‖x‖ = 0 := by
  rw [Pi.isUnit_iff, not_forall] at hx
  obtain ⟨v, hv⟩ := hx
  exact Finset.prod_eq_zero_iff.2 ⟨v, Finset.mem_univ v, by simpa [isUnit_iff_ne_zero] using hv⟩

/-- The product formula for the infinite adele ring. This is the adelic version of
`NumberField.InfinitePlace.prod_eq_abs_norm`. -/
/-
**NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.InfiniteAdeleRing`。
形式化陈述：coe_norm_eq_abs_norm [NumberField K] (x : K) : ‖algebraMap K K∞ x‖ = |Alge
bra.norm Rat x|
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
· 使用定理 `NumberField.InfinitePlace.prod_eq_abs_norm`：prod_eq_abs_norm (x : K) : ∏
 w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm Rat x)

--- 原说明 ---
The product formula for the infinite adele ring. This is the adelic version of
`NumberField.InfinitePlace.prod_eq_abs_norm`.
-/
theorem coe_norm_eq_abs_norm [NumberField K] (x : K) :
    ‖algebraMap K K∞ x‖ = |Algebra.norm ℚ x| := by
  simpa [-Rat.cast_abs, norm_def] using! InfinitePlace.prod_eq_abs_norm x

end InfiniteAdeleRing

end NumberField

