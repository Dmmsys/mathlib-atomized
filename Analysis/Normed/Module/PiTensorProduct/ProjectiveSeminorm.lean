/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, David Gross, Davood Haji Taghi Tehrani
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Projective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a normed field and `E` be a family of normed `𝕜`-vector spaces `Eᵢ`,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, Eᵢ`, which we call the
"projective seminorm". For `x` an element of `⨂[𝕜] i, Eᵢ`, its projective seminorm is the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.

In particular, every norm `‖.‖` on `⨂[𝕜] i, Eᵢ` satisfying `‖⨂ₜ[𝕜] i, m i‖ ≤ Π i, ‖m i‖`
for every `m` in `Π i, Eᵢ` is bounded above by the projective seminorm.

## Main definitions

* `PiTensorProduct.projectiveSeminorm`: The projective seminorm on `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.liftEquiv`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as a continuous linear equivalence.
* `PiTensorProduct.liftIsometry`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as an isometric linear equivalence.
* `PiTensorProduct.tprodL`: The canonical continuous multilinear map from `E = Πᵢ Eᵢ`
  to `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.mapL`: The continuous linear map from `⨂[𝕜] i, Eᵢ` to `⨂[𝕜] i, E'ᵢ`
  induced by a family of continuous linear maps `Eᵢ →L[𝕜] E'ᵢ`.
* `PiTensorProduct.mapLMultilinear`: The continuous multilinear map from
  `Πᵢ (Eᵢ →L[𝕜] E'ᵢ)` to `(⨂[𝕜] i, Eᵢ) →L[𝕜] (⨂[𝕜] i, E'ᵢ)` sending a family
  `f` to `PiTensorProduct.mapL f`.

## Main results

* `PiTensorProduct.norm_eval_le_projectiveSeminorm`: If `f` is a continuous multilinear map on
  `E = Π i, Eᵢ` and `x` is in `⨂[𝕜] i, Eᵢ`, then `‖f.lift x‖ ≤ projectiveSeminorm x * ‖f‖`.
* `PiTensorProduct.mapL_opNorm`: If `f` is a family of continuous linear maps
  `fᵢ : Eᵢ →L[𝕜] Fᵢ`, then `‖PiTensorProduct.mapL f‖ ≤ ∏ i, ‖fᵢ‖`.
* `PiTensorProduct.opNorm_mapLMultilinear_le` : If `F` is a normed vecteor space, then
  `‖mapLMultilinear 𝕜 E F‖ ≤ 1`.

## TODO
* If the base field is `ℝ` or `ℂ` (or more generally if the injection of `Eᵢ` into its bidual is
  an isometry for every `i`), then we have `projectiveSeminorm ⨂ₜ[𝕜] i, mᵢ = Π i, ‖mᵢ‖`.
* If all `Eᵢ` are separated and satisfy `SeparatingDual`, then the seminorm on
  `⨂[𝕜] i, Eᵢ` is a norm.
* Adapt the remaining functoriality constructions/properties from `PiTensorProduct`.

-/

@[expose] public section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*}
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]

open scoped TensorProduct

namespace PiTensorProduct

section NormedField

variable [NormedField 𝕜]

/-- A lift of the projective seminorm to `FreeAddMonoid (𝕜 × Π i, Eᵢ)`, useful to prove the
properties of `projectiveSeminorm`. -/
/-
**PiTensorProduct.projectiveSeminormAux** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProdu
ct`。
形式化陈述：projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lift of the projective seminorm to `FreeAddMonoid (𝕜 × Π i, Eᵢ)`, useful to pr
ove the
properties of `projectiveSeminorm`.
-/
def projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) → ℝ :=
  fun p ↦ (p.toList.map (fun p ↦ ‖p.1‖ * ∏ i, ‖p.2 i‖)).sum
/-
**PiTensorProduct.projectiveSeminormAux_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `PiTens
orProduct`。
形式化陈述：projectiveSeminormAux_nonneg (p : FreeAddMonoid (𝕜 × Π i, E i)) : 0 <= pro
jectiveSeminormAux p
参数：p : FreeAddMonoid (𝕜 × Π i, E i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sum_nonneg`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Preorde
r M] [AddLeftMono M] {l : List M}, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
-/
theorem projectiveSeminormAux_nonneg (p : FreeAddMonoid (𝕜 × Π i, E i)) :
    0 ≤ projectiveSeminormAux p := by
  refine List.sum_nonneg fun a ↦ ?_
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  intro x m _ h
  simpa [← h] using by positivity
/-
**PiTensorProduct.projectiveSeminormAux_add_le** 是 Mathlib 中的一个定理，位于命名空间 `PiTens
orProduct`。
形式化陈述：projectiveSeminormAux_add_le (p q : FreeAddMonoid (𝕜 × Π i, E i)) : projec
tiveSeminormAux (p + q) <= projectiveSeminormAux p + projectiveSeminormAux q
参数：p q : FreeAddMonoid (𝕜 × Π i, E i)。
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
· 使用定理 `List.sum_append`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Zero α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 + x2) 0]   [Std.Associative fun x1 x2 => x1 
+ x2]…
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `AddSemigroup.to_isLawfulIdentity`：∀ {M : Type u_4} [inst : AddZeroClass 
M], Std.LawfulIdentity (fun x1 x2 => x1 + x2) 0
· 使用定理 `AddSemigroup.to_isAssociative`：∀ {α : Type u_1} [inst : AddSemigroup α],
 Std.Associative fun x1 x2 => x1 + x2
-/
theorem projectiveSeminormAux_add_le (p q : FreeAddMonoid (𝕜 × Π i, E i)) :
    projectiveSeminormAux (p + q) ≤ projectiveSeminormAux p + projectiveSeminormAux q := by
  simp [projectiveSeminormAux]
/-
**PiTensorProduct.projectiveSeminormAux_smul** 是 Mathlib 中的一个定理，位于命名空间 `PiTensor
Product`。
形式化陈述：projectiveSeminormAux_smul (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) : pr
ojectiveSeminormAux (p.map (fun (y : 𝕜 × Π i, E i) => (a * y.1, y.2))) = ‖a‖ * p
rojectiveSeminormAux p
参数：p : FreeAddMonoid (𝕜 × Π i, E i)；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `List.sum_map_mul_left`：sum_map_mul_left : (l.map fun b => r * f b).sum =
 r * (l.map f).sum
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projectiveSeminormAux_smul (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) :
    projectiveSeminormAux (p.map (fun (y : 𝕜 × Π i, E i) ↦ (a * y.1, y.2))) =
    ‖a‖ * projectiveSeminormAux p := by
  simp [projectiveSeminormAux, Function.comp_def, mul_assoc, List.sum_map_mul_left]

variable [∀ i, NormedSpace 𝕜 (E i)]
/-
**PiTensorProduct.bddBelow_projectiveSemiNormAux** 是 Mathlib 中的一个定理，位于命名空间 `PiTe
nsorProduct`。
形式化陈述：bddBelow_projectiveSemiNormAux (x : ⨂[𝕜] i, E i) : BddBelow (Set.range (fu
n (p : lifts x) => projectiveSeminormAux p.1))
参数：x : ⨂[𝕜] i, E i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bddBelow_projectiveSemiNormAux (x : ⨂[𝕜] i, E i) :
    BddBelow (Set.range (fun (p : lifts x) ↦ projectiveSeminormAux p.1)) :=
  ⟨0, by simp [mem_lowerBounds, projectiveSeminormAux_nonneg]⟩
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Norm (⨂[𝕜] i, E i) :=
  ⟨fun x ↦ iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.val)⟩
/-
**PiTensorProduct.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：norm_def (x : ⨂[𝕜] i, E i) : ‖x‖ = iInf (fun (p : lifts x) => projectiveSe
minormAux p.val)
参数：x : ⨂[𝕜] i, E i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (x : ⨂[𝕜] i, E i) :
    ‖x‖ = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.val) := rfl

@[deprecated (since := "2026-06-10")] alias projectiveSeminormFun := norm
/-
**PiTensorProduct.projectiveSeminorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPro
duct`。
形式化陈述：projectiveSeminorm_zero : ‖(0 : ⨂[𝕜] i, E i)‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `PiTensorProduct.bddBelow_projectiveSemiNormAux`：bddBelow_projectiveSemiN
ormAux (x : ⨂[𝕜] i, E i) : BddBelow (Set.range (fun (p : lifts x) => projectiveS
eminormAux p.1))
· 使用引理 `PiTensorProduct.lifts_zero`：lifts_zero : 0 in lifts (0 : ⨂[R] i, s i)
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `PiTensorProduct.instNonemptyElemFreeAddMonoidProdForallLifts`：∀ {ι : Typ
e u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : 
ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.projectiveSeminormAux_nonneg`：projectiveSeminormAux_nonn
eg (p : FreeAddMonoid (𝕜 × Π i, E i)) : 0 <= projectiveSeminormAux p
-/
theorem projectiveSeminorm_zero : ‖(0 : ⨂[𝕜] i, E i)‖ = 0 :=
  le_antisymm (ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨0, lifts_zero⟩)
    (le_ciInf (fun p ↦ projectiveSeminormAux_nonneg p.val))
/-
**PiTensorProduct.projectiveSeminorm_add_le** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorP
roduct`。
形式化陈述：projectiveSeminorm_add_le (x y : ⨂[𝕜] i, E i) : ‖x + y‖ <= ‖x‖ + ‖y‖
参数：x y : ⨂[𝕜] i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciInf_add_ciInf`：∀ {α : Type u_1} {ι : Sort u_2} {ι' : Sort u_3} [Non
empty ι] [Nonempty ι'] [inst : ConditionallyCompleteLattice α]   [inst_1 : AddGr
oup α] […
· 使用定理 `PiTensorProduct.instNonemptyElemFreeAddMonoidProdForallLifts`：∀ {ι : Typ
e u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : 
ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _r…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ciInf_le_of_le`：ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c 
: ι) (h : f c <= a) : iInf f <= a
· 使用定理 `PiTensorProduct.bddBelow_projectiveSemiNormAux`：bddBelow_projectiveSemiN
ormAux (x : ⨂[𝕜] i, E i) : BddBelow (Set.range (fun (p : lifts x) => projectiveS
eminormAux p.1))
· 使用引理 `PiTensorProduct.lifts_add`：lifts_add {x y : ⨂[R] i, s i} {p q : FreeAddM
onoid (R × Π i, s i)} (hp : p in lifts x) (hq : q in lifts y) : p + q in lifts (
x + y)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `PiTensorProduct.projectiveSeminormAux_add_le`：projectiveSeminormAux_add_
le (p q : FreeAddMonoid (𝕜 × Π i, E i)) : projectiveSeminormAux (p + q) <= proje
ctiveSeminormAux p + projectiveSem…
-/
theorem projectiveSeminorm_add_le (x y : ⨂[𝕜] i, E i) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  le_ciInf_add_ciInf (fun p q ↦ ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
    ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))
/-
**PiTensorProduct.projectiveSeminorm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `PiTensor
Product`。
形式化陈述：projectiveSeminorm_smul_le (a : 𝕜) (x : ⨂[𝕜] i, E i) : ‖a • x‖ <= ‖a‖ * ‖x
‖
参数：a : 𝕜；x : ⨂[𝕜] i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.mul_iInf_of_nonneg`：Real.mul_iInf_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (r * ⨅ i, f i) = ⨅ i, r * f i
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `PiTensorProduct.instNonemptyElemFreeAddMonoidProdForallLifts`：∀ {ι : Typ
e u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : 
ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _r…
· 使用引理 `PiTensorProduct.lifts_smul`：lifts_smul {x : ⨂[R] i, s i} {p : FreeAddMon
oid (R × Π i, s i)} (h : p in lifts x) (a : R) : p.map (fun (y : R × Π i, s i) =
> (a * y.1, y.2)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `PiTensorProduct.projectiveSeminormAux_smul`：projectiveSeminormAux_smul (
p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) : projectiveSeminormAux (p.map (fun (y
 : 𝕜 × Π i, E i) => (a * y.1, y.…
· 使用定理 `ciInf_le_of_le`：ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c 
: ι) (h : f c <= a) : iInf f <= a
· 使用定理 `PiTensorProduct.bddBelow_projectiveSemiNormAux`：bddBelow_projectiveSemiN
ormAux (x : ⨂[𝕜] i, E i) : BddBelow (Set.range (fun (p : lifts x) => projectiveS
eminormAux p.1))
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem projectiveSeminorm_smul_le (a : 𝕜) (x : ⨂[𝕜] i, E i) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  simp only [norm_def, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun p ↦ ?_
  simpa [projectiveSeminormAux_smul] using
    ciInf_le_of_le (bddBelow_projectiveSemiNormAux _) ⟨_, lifts_smul p.2 a⟩ (le_refl _)

/-- The projective seminorm on `⨂[𝕜] i, Eᵢ`. It sends an element `x` of `⨂[𝕜] i, Eᵢ` to the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`. -/
/-
**PiTensorProduct.projectiveSeminorm** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`
。
形式化陈述：projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.projectiveSeminorm_zero`：projectiveSeminorm_zero : ‖(0 :
 ⨂[𝕜] i, E i)‖ = 0
· 使用定理 `PiTensorProduct.projectiveSeminorm_add_le`：projectiveSeminorm_add_le (x 
y : ⨂[𝕜] i, E i) : ‖x + y‖ <= ‖x‖ + ‖y‖
· 使用定理 `PiTensorProduct.projectiveSeminorm_smul_le`：projectiveSeminorm_smul_le (
a : 𝕜) (x : ⨂[𝕜] i, E i) : ‖a • x‖ <= ‖a‖ * ‖x‖

--- 原说明 ---
The projective seminorm on `⨂[𝕜] i, Eᵢ`. It sends an element `x` of `⨂[𝕜] i, Eᵢ`
 to the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, 
Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.
-/
noncomputable def projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) := .ofSMulLE
    norm projectiveSeminorm_zero projectiveSeminorm_add_le projectiveSeminorm_smul_le
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SeminormedAddCommGroup (⨂[𝕜] i, E i) :=
  fast_instance% AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm
/-
**PiTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedSpace 𝕜 (⨂[𝕜] i, E i) := ⟨projectiveSeminorm_smul_le⟩

@[deprecated norm_def (since := "2026-06-10")]
/-
**PiTensorProduct.projectiveSeminorm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPr
oduct`。
形式化陈述：projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) : projectiveSeminorm x = iInf (
fun (p : lifts x) => projectiveSeminormAux p.1)
参数：x : ⨂[𝕜] i, E i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    projectiveSeminorm x = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.1) := rfl
/-
**PiTensorProduct.projectiveSeminorm_tprod_le** 是 Mathlib 中的一个定理，位于命名空间 `PiTenso
rProduct`。
形式化陈述：projectiveSeminorm_tprod_le (m : Π i, E i) : ‖(⨂ₜ[𝕜] i, m i)‖ <= ∏ i, ‖m i
‖
参数：m : Π i, E i。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `PiTensorProduct.bddBelow_projectiveSemiNormAux`：bddBelow_projectiveSemiN
ormAux (x : ⨂[𝕜] i, E i) : BddBelow (Set.range (fun (p : lifts x) => projectiveS
eminormAux p.1))
· 使用定理 `PiTensorProduct.norm_def`：norm_def (x : ⨂[𝕜] i, E i) : ‖x‖ = iInf (fun (
p : lifts x) => projectiveSeminormAux p.val)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
    ‖(⨂ₜ[𝕜] i, m i)‖ ≤ ∏ i, ‖m i‖ := by
   have hle := ciInf_le (bddBelow_projectiveSemiNormAux (⨂ₜ[𝕜] i, m i))
    ⟨FreeAddMonoid.of (1, m), by simp [mem_lifts_iff]⟩
   grw [norm_def, hle]
   simp [projectiveSeminormAux]

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

/-
**PiTensorProduct.norm_eval_le_projectiveSeminorm** 是 Mathlib 中的一个定理，位于命名空间 `PiT
ensorProduct`。
形式化陈述：norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G] [No
rmedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E i) : ‖lift f.
toMultilinearMap x‖ <= ‖f‖ * ‖x‖
参数：f : ContinuousMultilinearMap 𝕜 E G；x : ⨂[𝕜] i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.norm_def`：norm_def (x : ⨂[𝕜] i, E i) : ‖x‖ = iInf (fun (
p : lifts x) => projectiveSeminormAux p.val)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.iInf_mul_of_nonneg`：Real.iInf_mul_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (⨅ i, f i) * r = ⨅ i, f i * r
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `PiTensorProduct.instNonemptyElemFreeAddMonoidProdForallLifts`：∀ {ι : Typ
e u_1} {R : Type u_4} [inst : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : 
ι) → AddCommMonoid (s i)]   [inst_2 : (i : ι) → _r…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `PiTensorProduct.mem_lifts_iff`：mem_lifts_iff (x : ⨂[R] i, s i) (p : Free
AddMonoid (R × Π i, s i)) : p in lifts x ↔ List.sum (List.map (fun x => x.1 • ⨂ₜ
[R] i, x.2 i) p.toL…
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `List.sum_map_hom`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst :
 AddMonoid M] [inst_1 : AddMonoid N] (L : List ι) (f : ι → M)   {G : Type u_8} [
inst_2…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Multiset.sum_coe`：∀ {M : Type u_3} [inst : AddCommMonoid M] (l : List M)
, (↑l).sum = l.sum
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `norm_multiset_sum_le`：norm_multiset_sum_le {E} [SeminormedAddCommGroup E
] (m : Multiset E) : ‖m.sum‖ <= (m.map fun x => ‖x‖).sum
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.smul_sum`：List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (
r • ·)).sum
· 使用定理 `List.Forall₂.sum_le_sum`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 :
 Preorder M] [AddRightMono M] [AddLeftMono M] {l₁ l₂ : List M},   List.Forall₂ (
fun x1 x2 => …
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
（共 39 条，此处仅展示前 30 条）
-/
theorem norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * ‖x‖ := by
  rw [norm_def, mul_comm, Real.iInf_mul_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun ⟨p, hp⟩ ↦ ?_
  rw! [← ((mem_lifts_iff x p).mp hp), ← List.sum_map_hom, ← Multiset.sum_coe]
  grw [norm_multiset_sum_le]
  simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
  refine List.Forall₂.sum_le_sum ?_
  simpa [norm_smul, ← mul_assoc, mul_comm ‖f‖ _] using
    fun a m _ ↦ mul_le_mul_of_nonneg_left (f.le_opNorm _) (norm_nonneg _)

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F)

/-- The linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
induced by `PiTensorProduct.lift`, for every normed space `F`.
-/
@[simps]
/-
**PiTensorProduct.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) ->L[𝕜] F wh
ere toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.norm_eval_le_projectiveSeminorm`：norm_eval_le_projective
Seminorm {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (f : Continuou
sMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E…

--- 原说明 ---
The linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ
) →L[𝕜] F`
induced by `PiTensorProduct.lift`, for every normed space `F`.
-/
noncomputable def liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F where
  toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x ↦
    norm_eval_le_projectiveSeminorm f x
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x ↦
    ContinuousLinearMap.le_opNorm_of_le _ (projectiveSeminorm_tprod_le x)
  left_inv f := by ext; simp
  right_inv l := by
    rw [← ContinuousLinearMap.coe_inj]
    ext; simp

/-- For a normed space `F`, we have constructed in `PiTensorProduct.liftEquiv` the canonical
linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
(induced by `PiTensorProduct.lift`). Here we give the upgrade of this equivalence to
an isometric linear equivalence; in particular, it is a continuous linear equivalence. -/
/-
**PiTensorProduct.liftIsometry** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：liftIsometry : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) ->L[𝕜] 
F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a normed space `F`, we have constructed in `PiTensorProduct.liftEquiv` the c
anonical
linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L
[𝕜] F`
(induced by `PiTensorProduct.lift`). Here we give the upgrade of this equivalenc
e to
an isometric linear equivalence; in particular, it is a continuous linear equiva
lence.
-/
noncomputable def liftIsometry : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F :=
  LinearIsometryEquiv.ofBounds (liftEquiv 𝕜 E F)
  (fun f ↦ LinearMap.mkContinuous_norm_le _ (norm_nonneg f) (norm_eval_le_projectiveSeminorm f))
  (fun f ↦ by
      rw [liftEquiv_symm_apply]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable {𝕜 E F}

@[simp]
/-
**PiTensorProduct.liftIsometry_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPr
oduct`。
形式化陈述：liftIsometry_apply_apply (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i,
 E i) : liftIsometry 𝕜 E F f x = lift f.toMultilinearMap x
参数：f : ContinuousMultilinearMap 𝕜 E F；x : ⨂[𝕜] i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.norm_eval_le_projectiveSeminorm`：norm_eval_le_projective
Seminorm {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (f : Continuou
sMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E…
· 使用定理 `PiTensorProduct.liftEquiv_apply`：∀ {ι : Type u_1} [inst : Fintype ι] (𝕜 
: Type u_2) (E : ι → Type u_3) [inst_1 : (i : ι) → SeminormedAddCommGroup (E i)]
   [inst_2 : Nontrivi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftIsometry_apply_apply (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    liftIsometry 𝕜 E F f x = lift f.toMultilinearMap x := by
  simp [LinearIsometryEquiv.ofBounds, liftIsometry]

variable (𝕜) in
/-- The canonical continuous multilinear map from `E = Πᵢ Eᵢ` to `⨂[𝕜] i, Eᵢ`. -/
@[simps! toFun]
/-
**PiTensorProduct.tprodL** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical continuous multilinear map from `E = Πᵢ Eᵢ` to `⨂[𝕜] i, Eᵢ`.
-/
noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i) :=
  (liftIsometry 𝕜 E _).symm (ContinuousLinearMap.id 𝕜 _)

@[simp]
/-
**PiTensorProduct.tprodL_coe** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：tprodL_coe : (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.tprodL_toFun`：∀ {ι : Type u_1} [inst : Fintype ι] (𝕜 : T
ype u_2) {E : ι → Type u_3} [inst_1 : (i : ι) → SeminormedAddCommGroup (E i)]   
[inst_2 : Nontrivi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tprodL_coe : (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E) := by
  ext; simp

@[simp]
/-
**PiTensorProduct.liftIsometry_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPro
duct`。
形式化陈述：liftIsometry_symm_apply (l : (⨂[𝕜] i, E i) ->L[𝕜] F) : (liftIsometry 𝕜 E F
).symm l = l.compContinuousMultilinearMap (tprodL 𝕜)
参数：l : (⨂[𝕜] i, E i) ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem liftIsometry_symm_apply (l : (⨂[𝕜] i, E i) →L[𝕜] F) :
    (liftIsometry 𝕜 E F).symm l = l.compContinuousMultilinearMap (tprodL 𝕜) := by
  rfl

@[simp]
/-
**PiTensorProduct.liftIsometry_tprodL** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct
`。
形式化陈述：liftIsometry_tprodL : liftIsometry 𝕜 E _ (tprodL 𝕜) = ContinuousLinearMap.
id 𝕜 (⨂[𝕜] i, E i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.liftIsometry_apply_apply`：liftIsometry_apply_apply (f : 
ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) : liftIsometry 𝕜 E F f x = lif
t f.toMultilinearMap x
· 使用定理 `PiTensorProduct.tprodL_coe`：tprodL_coe : (tprodL 𝕜).toMultilinearMap = t
prod 𝕜 (s
· 使用定理 `PiTensorProduct.lift_tprod`：lift_tprod : lift (tprod R : MultilinearMap 
R s _) = LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftIsometry_tprodL :
    liftIsometry 𝕜 E _ (tprodL 𝕜) = ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i) := by
  ext; simp

section map

variable {E' E'' : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
variable [∀ i, SeminormedAddCommGroup (E'' i)] [∀ i, NormedSpace 𝕜 (E'' i)]
variable (g : Π i, E' i →L[𝕜] E'' i) (f : Π i, E i →L[𝕜] E' i)

/-- Let `Eᵢ` and `E'ᵢ` be two families of normed `𝕜`-vector spaces.
Let `f` be a family of continuous `𝕜`-linear maps between `Eᵢ` and `E'ᵢ`, i.e.
`f : Πᵢ Eᵢ →L[𝕜] E'ᵢ`, then there is an induced continuous linear map
`⨂ᵢ Eᵢ → ⨂ᵢ E'ᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`. -/
/-
**PiTensorProduct.mapL** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：mapL : (⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E' i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `Eᵢ` and `E'ᵢ` be two families of normed `𝕜`-vector spaces.
Let `f` be a family of continuous `𝕜`-linear maps between `Eᵢ` and `E'ᵢ`, i.e.
`f : Πᵢ Eᵢ →L[𝕜] E'ᵢ`, then there is an induced continuous linear map
`⨂ᵢ Eᵢ → ⨂ᵢ E'ᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`.
-/
noncomputable def mapL : (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  liftIsometry 𝕜 E _ <| (tprodL 𝕜).compContinuousLinearMap f

@[simp]
/-
**PiTensorProduct.mapL_coe** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：mapL_coe : (mapL f).toLinearMap = map (fun i => (f i).toLinearMap)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `PiTensorProduct.liftIsometry_apply_apply`：liftIsometry_apply_apply (f : 
ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) : liftIsometry 𝕜 E F f x = lif
t f.toMultilinearMap x
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.tprodL_toFun`：∀ {ι : Type u_1} [inst : Fintype ι] (𝕜 : T
ype u_2) {E : ι → Type u_3} [inst_1 : (i : ι) → SeminormedAddCommGroup (E i)]   
[inst_2 : Nontrivi…
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapL_coe : (mapL f).toLinearMap = map (fun i ↦ (f i).toLinearMap) := by
  ext; simp [mapL]

@[simp]
/-
**PiTensorProduct.mapL_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = map (fun i => (f i).toLinearMap)
 x
参数：x : ⨂[𝕜] i, E i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = map (fun i ↦ (f i).toLinearMap) x := by
  rfl

/-- Given submodules `pᵢ ⊆ Eᵢ`, this is the natural map: `⨂[𝕜] i, pᵢ → ⨂[𝕜] i, Eᵢ`.
This is the continuous version of `PiTensorProduct.mapIncl`. -/
@[simp]
/-
**PiTensorProduct.mapLIncl** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：mapLIncl (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) ->L[𝕜] ⨂[𝕜] i, E i
参数：p : Π i, Submodule 𝕜 (E i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given submodules `pᵢ ⊆ Eᵢ`, this is the natural map: `⨂[𝕜] i, pᵢ → ⨂[𝕜] i, Eᵢ`.
This is the continuous version of `PiTensorProduct.mapIncl`.
-/
noncomputable def mapLIncl (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) →L[𝕜] ⨂[𝕜] i, E i :=
  mapL fun (i : ι) ↦ (p i).subtypeL
/-
**PiTensorProduct.mapL_comp** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：mapL_comp : mapL (fun (i : ι) => g i ∘L f i) = mapL g ∘L mapL f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PiTensorProduct.mapL_coe`：mapL_coe : (mapL f).toLinearMap = map (fun i =
> (f i).toLinearMap)
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapL_comp : mapL (fun (i : ι) ↦ g i ∘L f i) = mapL g ∘L mapL f := by
  apply ContinuousLinearMap.coe_injective
  ext; simp
/-
**PiTensorProduct.liftIsometry_comp_mapL** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProd
uct`。
形式化陈述：liftIsometry_comp_mapL (h : ContinuousMultilinearMap 𝕜 E' F) : liftIsometr
y 𝕜 E' F h ∘L mapL f = liftIsometry 𝕜 E F (h.compContinuousLinearMap f)
参数：h : ContinuousMultilinearMap 𝕜 E' F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `PiTensorProduct.mapL_coe`：mapL_coe : (mapL f).toLinearMap = map (fun i =
> (f i).toLinearMap)
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.liftIsometry_apply_apply`：liftIsometry_apply_apply (f : 
ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) : liftIsometry 𝕜 E F f x = lif
t f.toMultilinearMap x
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftIsometry_comp_mapL (h : ContinuousMultilinearMap 𝕜 E' F) :
    liftIsometry 𝕜 E' F h ∘L mapL f = liftIsometry 𝕜 E F (h.compContinuousLinearMap f) := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]
/-
**PiTensorProduct.mapL_id** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：mapL_id : mapL (fun i => ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinea
rMap.id _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.mapL_coe`：mapL_coe : (mapL f).toLinearMap = map (fun i =
> (f i).toLinearMap)
· 使用定理 `PiTensorProduct.map_id`：map_id : map (fun i => (LinearMap.id : s i ->ₗ[R
] s i)) = .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapL_id : mapL (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _ := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]
/-
**PiTensorProduct.mapL_one** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：mapL_one : mapL (fun (i : ι) => (1 : E i ->L[𝕜] E i)) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.mapL_id`：mapL_id : mapL (fun i => ContinuousLinearMap.id
 𝕜 (E i)) = ContinuousLinearMap.id _ _
-/
theorem mapL_one : mapL (fun (i : ι) ↦ (1 : E i →L[𝕜] E i)) = 1 :=
  mapL_id
/-
**PiTensorProduct.mapL_mul** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：mapL_mul (f₁ f₂ : Π i, E i ->L[𝕜] E i) : mapL (fun i => f₁ i * f₂ i) = map
L f₁ * mapL f₂
参数：f₁ f₂ : Π i, E i ->L[𝕜] E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.mapL_comp`：mapL_comp : mapL (fun (i : ι) => g i ∘L f i) 
= mapL g ∘L mapL f
-/
theorem mapL_mul (f₁ f₂ : Π i, E i →L[𝕜] E i) :
    mapL (fun i ↦ f₁ i * f₂ i) = mapL f₁ * mapL f₂ :=
  mapL_comp f₁ f₂

/-- Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = E'`. -/
@[simps]
/-
**PiTensorProduct.mapLMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：mapLMonoidHom : (Π i, E i ->L[𝕜] E i) ->* ((⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E 
i) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.mapL_one`：mapL_one : mapL (fun (i : ι) => (1 : E i ->L[𝕜
] E i)) = 1
· 使用定理 `PiTensorProduct.mapL_mul`：mapL_mul (f₁ f₂ : Π i, E i ->L[𝕜] E i) : mapL 
(fun i => f₁ i * f₂ i) = mapL f₁ * mapL f₂

--- 原说明 ---
Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = E'`.
-/
noncomputable def mapLMonoidHom : (Π i, E i →L[𝕜] E i) →* ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E i) where
  toFun := mapL
  map_one' := mapL_one
  map_mul' := mapL_mul

@[simp]
/-
**PiTensorProduct.mapL_pow** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {𝕜 : Type u_2} {E : ι → Type u_3} [ins
t_1 : (i : ι) → SeminormedAddCommGroup (E i)]   [inst_2 : NontriviallyNormedFiel
d 𝕜] [inst_3 : (i : ι) → NormedSpace 𝕜 (E i)] (f : (i : ι) → E i →L[𝕜] E i) (n :
 ℕ),   PiTensorProduct.mapL (f ^ n) = PiTensorProduct.mapL f ^ n
参数：i : ι；E i；i : ι；E i；f : (i : ι) → E i →L[𝕜] E i；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
protected theorem mapL_pow (f : Π i, E i →L[𝕜] E i) (n : ℕ) :
    mapL (f ^ n) = mapL f ^ n := MonoidHom.map_pow mapLMonoidHom f n

-- We redeclare `ι` here, and later dependent arguments,
-- to avoid the `[Fintype ι]` assumption present throughout the rest of the file.
open Function in
/-
**PiTensorProduct.mapL_add_smul_aux** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mapL_add_smul_aux {ι : Type*}
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {E' : ι → Type*} [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
    (f : (i : ι) → E i →L[𝕜] E' i) [DecidableEq ι] (i : ι) (u : E i →L[𝕜] E' i) :
    (fun j ↦ (update f i u j).toLinearMap) =
      update (fun j ↦ (f j).toLinearMap) i u.toLinearMap := by
  grind

open Function in
/-
**PiTensorProduct.mapL_add** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {𝕜 : Type u_2} {E : ι → Type u_3} [ins
t_1 : (i : ι) → SeminormedAddCommGroup (E i)]   [inst_2 : NontriviallyNormedFiel
d 𝕜] [inst_3 : (i : ι) → NormedSpace 𝕜 (E i)] {E' : ι → Type u_5}   [inst_4 : (i
 : ι) → SeminormedAddCommGroup (E' i)] [inst_5 : (i : ι) → NormedSpace 𝕜 (E' i)]
   (f : (i : ι) → E i →L[𝕜] E' i) [inst_6 : DecidableEq ι] (i : ι) (u v : E i →L
[𝕜] E' i),   PiTensorProduct.mapL (Function.update f i (u + v)) =     PiTensorPr
oduct.mapL (Function.update f i u) + PiTensorProduct.mapL (Function.update f i v
)
参数：i : ι；E i；i : ι；E i；i : ι；E' i；i : ι；E' i；f : (i : ι) → E i →L[𝕜] E' i；i : ι；
u v : E i →L[𝕜] E' i；Function.update f i (u + v)；Function.update f i u；Function.
update f i v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.mapL_apply`：mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = ma
p (fun i => (f i).toLinearMap) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSemino
rm.0.PiTensorProduct.mapL_add_smul_aux`：∀ {𝕜 : Type u_2} [inst : NontriviallyNor
medField 𝕜] {ι : Type u_7} {E : ι → Type u_8}   [inst_1 : (i : ι) → SeminormedAd
dCommGroup (E i)] [i…
· 使用定理 `PiTensorProduct.map_update_add`：∀ {ι : Type u_1} {R : Type u_4} [inst : 
CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [i
nst_2 : (i : ι) → _r…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mapL_add [DecidableEq ι] (i : ι) (u v : E i →L[𝕜] E' i) :
    mapL (update f i (u + v)) = mapL (update f i u) + mapL (update f i v) := by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_add]

open Function in
/-
**PiTensorProduct.mapL_smul** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {𝕜 : Type u_2} {E : ι → Type u_3} [ins
t_1 : (i : ι) → SeminormedAddCommGroup (E i)]   [inst_2 : NontriviallyNormedFiel
d 𝕜] [inst_3 : (i : ι) → NormedSpace 𝕜 (E i)] {E' : ι → Type u_5}   [inst_4 : (i
 : ι) → SeminormedAddCommGroup (E' i)] [inst_5 : (i : ι) → NormedSpace 𝕜 (E' i)]
   (f : (i : ι) → E i →L[𝕜] E' i) [inst_6 : DecidableEq ι] (i : ι) (c : 𝕜) (u : 
E i →L[𝕜] E' i),   PiTensorProduct.mapL (Function.update f i (c • u)) = c • PiTe
nsorProduct.mapL (Function.update f i u)
参数：i : ι；E i；i : ι；E i；i : ι；E' i；i : ι；E' i；f : (i : ι) → E i →L[𝕜] E' i；i : ι；
c : 𝕜；u : E i →L[𝕜] E' i；Function.update f i (c • u)；Function.update f i u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.mapL_apply`：mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = ma
p (fun i => (f i).toLinearMap) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSemino
rm.0.PiTensorProduct.mapL_add_smul_aux`：∀ {𝕜 : Type u_2} [inst : NontriviallyNor
medField 𝕜] {ι : Type u_7} {E : ι → Type u_8}   [inst_1 : (i : ι) → SeminormedAd
dCommGroup (E i)] [i…
· 使用定理 `PiTensorProduct.map_update_smul`：∀ {ι : Type u_1} {R : Type u_4} [inst :
 CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [
inst_2 : (i : ι) → _r…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mapL_smul [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i →L[𝕜] E' i) :
    mapL (update f i (c • u)) = c • mapL (update f i u) := by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_smul]
/-
**PiTensorProduct.opNorm_mapL** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：opNorm_mapL : ‖mapL f‖ <= ∏ i, ‖f i‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearMap.opNorm_le_iff`：opNorm_le_iff {f : E ->SL[σ₁₂] F} {M 
: Real} (hMp : 0 <= M) : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M * ‖x‖
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `PiTensorProduct.norm_eval_le_projectiveSeminorm`：norm_eval_le_projective
Seminorm {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (f : Continuou
sMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousMultilinearMap.opNorm_le_iff`：opNorm_le_iff {f : ContinuousMul
tilinearMap 𝕜 E G} {C : Real} (hC : 0 <= C) : ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * 
∏ i, ‖m i‖
· 使用定理 `PiTensorProduct.projectiveSeminorm_tprod_le`：projectiveSeminorm_tprod_le
 (m : Π i, E i) : ‖(⨂ₜ[𝕜] i, m i)‖ <= ∏ i, ‖m i‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem opNorm_mapL : ‖mapL f‖ ≤ ∏ i, ‖f i‖ := by
  refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr fun x ↦ ?_
  apply le_trans (norm_eval_le_projectiveSeminorm ..) (mul_le_mul_of_nonneg_right _ (norm_nonneg x))
  refine (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr fun m ↦ ?_
  apply le_trans (projectiveSeminorm_tprod_le fun i ↦ f i (m i))
  rw [← Finset.prod_mul_distrib]
  gcongr
  exact ContinuousLinearMap.le_opNorm _ _

variable (𝕜 E E')

/-- The tensor of a family of linear maps from `Eᵢ` to `E'ᵢ`, as a continuous multilinear map of
the family. -/
@[simps! toFun_apply]
/-
**PiTensorProduct.mapLMultilinear** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：mapLMultilinear : ContinuousMultilinearMap 𝕜 (fun (i : ι) => E i ->L[𝕜] E'
 i) ((⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E' i)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.mapL_add`：∀ {ι : Type u_1} [inst : Fintype ι] {𝕜 : Type 
u_2} {E : ι → Type u_3} [inst_1 : (i : ι) → SeminormedAddCommGroup (E i)]   [ins
t_2 : Nontrivi…
· 使用定理 `PiTensorProduct.mapL_smul`：∀ {ι : Type u_1} [inst : Fintype ι] {𝕜 : Type
 u_2} {E : ι → Type u_3} [inst_1 : (i : ι) → SeminormedAddCommGroup (E i)]   [in
st_2 : Nontrivi…

--- 原说明 ---
The tensor of a family of linear maps from `Eᵢ` to `E'ᵢ`, as a continuous multil
inear map of
the family.
-/
noncomputable def mapLMultilinear : ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ E i →L[𝕜] E' i)
    ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i) :=
  MultilinearMap.mkContinuous
  { toFun := mapL
    map_update_smul' := fun _ _ _ _ ↦ PiTensorProduct.mapL_smul _ _ _ _
    map_update_add' := fun _ _ _ _ ↦ PiTensorProduct.mapL_add _ _ _ _ }
  1 (fun f ↦ by rw [one_mul]; exact opNorm_mapL f)

variable {𝕜 E E'}
/-
**PiTensorProduct.opNorm_mapLMultilinear_le** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorP
roduct`。
形式化陈述：opNorm_mapLMultilinear_le : ‖mapLMultilinear 𝕜 E E'‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.mkContinuous_norm_le`：MultilinearMap.mkContinuous_norm_le
 (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C *
 ∏ i, ‖m i‖) : ‖f.mkConti…
· 使用定理 `PiTensorProduct.mapL_add`：∀ {ι : Type u_1} [inst : Fintype ι] {𝕜 : Type 
u_2} {E : ι → Type u_3} [inst_1 : (i : ι) → SeminormedAddCommGroup (E i)]   [ins
t_2 : Nontrivi…
· 使用定理 `PiTensorProduct.mapL_smul`：∀ {ι : Type u_1} [inst : Fintype ι] {𝕜 : Type
 u_2} {E : ι → Type u_3} [inst_1 : (i : ι) → SeminormedAddCommGroup (E i)]   [in
st_2 : Nontrivi…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem opNorm_mapLMultilinear_le : ‖mapLMultilinear 𝕜 E E'‖ ≤ 1 :=
  MultilinearMap.mkContinuous_norm_le _ zero_le_one _

end map

end NontriviallyNormedField

end PiTensorProduct

