/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Bilinear
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finiteness of the tensor product of (sub)modules

In this file we show that the supremum of two subalgebras that are finitely generated as modules,
is again finitely generated.

-/

public section

open Function (Surjective)
open Finsupp

namespace Submodule

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
  [AddCommMonoid N] [Module R M] [Module R N] {I : Submodule R N}

open TensorProduct LinearMap
/-- Every `x : N ⊗ M` is the image of some `y : J ⊗ M`, where `J` is a finitely generated
submodule of `N`, under the tensor product of the inclusion `J → N` and the identity `M → M`. -/
/-
**Submodule.exists_fg_le_eq_rTensor_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：exists_fg_le_eq_rTensor_subtype (x : N otimes M) : exists (J : Submodule R
 N) (_ : J.FG) (y : J otimes M), x = rTensor M J.subtype y
参数：x : N otimes M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `Submodule.fg_span_singleton`：fg_span_singleton (x : M) : FG (R ∙ x)
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_comp_apply`：rTensor_comp_apply (x : N otimes[R] M) : (
g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x)

--- 原说明 ---
Every `x : N ⊗ M` is the image of some `y : J ⊗ M`, where `J` is a finitely gene
rated
submodule of `N`, under the tensor product of the inclusion `J → N` and the iden
tity `M → M`.
-/
theorem exists_fg_le_eq_rTensor_subtype (x : N ⊗ M) :
    ∃ (J : Submodule R N) (_ : J.FG) (y : J ⊗ M), x = rTensor M J.subtype y := by
  induction x with
  | zero => exact ⟨⊥, fg_bot, 0, rfl⟩
  | tmul i m => exact ⟨R ∙ i, fg_span_singleton i, ⟨i, mem_span_singleton_self _⟩ ⊗ₜ[R] m, rfl⟩
  | add x₁ x₂ ihx₁ ihx₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ihx₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ihx₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂,
      rTensor M (J₁.inclusion le_sup_left) y₁ + rTensor M (J₂.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add, ← rTensor_comp_apply, ← rTensor_comp_apply]
    rfl
/-
**Submodule.exists_fg_le_subset_range_rTensor_subtype** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
形式化陈述：exists_fg_le_subset_range_rTensor_subtype (s : Set (N otimes[R] M)) (hs : 
s.Finite) : exists (J : Submodule R N) (_ : J.FG), s subseteq LinearMap.range (r
Tensor M J.subtype)
参数：s : Set (N otimes[R] M)；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_iSup`：fg_iSup {ι : Sort*} [Finite ι] (N : ι -> Submodule R 
M) (h : forall i, (N i).FG) : (iSup N).FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Submodule.exists_fg_le_eq_rTensor_subtype`：exists_fg_le_eq_rTensor_subty
pe (x : N otimes M) : exists (J : Submodule R N) (_ : J.FG) (y : J otimes M), x 
= rTensor M J.subtype y
-/
theorem exists_fg_le_subset_range_rTensor_subtype (s : Set (N ⊗[R] M)) (hs : s.Finite) :
    ∃ (J : Submodule R N) (_ : J.FG), s ⊆ LinearMap.range (rTensor M J.subtype) := by
  choose J fg y eq using exists_fg_le_eq_rTensor_subtype (R := R) (M := M) (N := N)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ ↦ fg _, fun x hx ↦
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply, ← rTensor_comp]; rfl

open TensorProduct LinearMap
/-- Every `x : I ⊗ M` is the image of some `y : J ⊗ M`, where `J ≤ I` is finitely generated,
under the tensor product of `J.inclusion ‹J ≤ I› : J → I` and the identity `M → M`. -/
/-
**Submodule.exists_fg_le_eq_rTensor_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：exists_fg_le_eq_rTensor_inclusion (x : I otimes M) : exists (J : Submodule
 R N) (_ : J.FG) (hle : J <= I) (y : J otimes M), x = rTensor M (J.inclusion hle
) y
参数：x : I otimes M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_fg_le_eq_rTensor_subtype`：exists_fg_le_eq_rTensor_subty
pe (x : N otimes M) : exists (J : Submodule R N) (_ : J.FG) (y : J otimes M), x 
= rTensor M J.subtype y
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Submodule.map_subtype_le`：map_subtype_le (p' : Submodule R p) : map p.su
btype p' <= p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_comp_apply`：rTensor_comp_apply (x : N otimes[R] M) : (
g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x)

--- 原说明 ---
Every `x : I ⊗ M` is the image of some `y : J ⊗ M`, where `J ≤ I` is finitely ge
nerated,
under the tensor product of `J.inclusion ‹J ≤ I› : J → I` and the identity `M → 
M`.
-/
theorem exists_fg_le_eq_rTensor_inclusion (x : I ⊗ M) :
    ∃ (J : Submodule R N) (_ : J.FG) (hle : J ≤ I) (y : J ⊗ M),
      x = rTensor M (J.inclusion hle) y := by
  obtain ⟨J, fg, y, rfl⟩ := exists_fg_le_eq_rTensor_subtype x
  refine ⟨J.map I.subtype, fg.map _, I.map_subtype_le J, rTensor M (I.subtype.submoduleMap J) y, ?_⟩
  rw [← LinearMap.rTensor_comp_apply]; rfl
/-
**Submodule.exists_fg_le_subset_range_rTensor_inclusion** 是 Mathlib 中的一个定理，位于命名空
间 `Submodule`。
形式化陈述：exists_fg_le_subset_range_rTensor_inclusion (s : Set (I otimes[R] M)) (hs 
: s.Finite) : exists (J : Submodule R N) (_ : J.FG) (hle : J <= I), s subseteq L
inearMap.range (rTensor M (J.inclusion hle))
参数：s : Set (I otimes[R] M)；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_iSup`：fg_iSup {ι : Sort*} [Finite ι] (N : ι -> Submodule R 
M) (h : forall i, (N i).FG) : (iSup N).FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Submodule.exists_fg_le_eq_rTensor_inclusion`：exists_fg_le_eq_rTensor_inc
lusion (x : I otimes M) : exists (J : Submodule R N) (_ : J.FG) (hle : J <= I) (
y : J otimes M), x = rTensor M (J…
-/
theorem exists_fg_le_subset_range_rTensor_inclusion (s : Set (I ⊗[R] M)) (hs : s.Finite) :
    ∃ (J : Submodule R N) (_ : J.FG) (hle : J ≤ I),
      s ⊆ LinearMap.range (rTensor M (J.inclusion hle)) := by
  choose J fg hle y eq using exists_fg_le_eq_rTensor_inclusion (M := M) (I := I)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ ↦ fg _, iSup_le fun _ ↦ hle _, fun x hx ↦
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply, ← rTensor_comp]; rfl

end Submodule

section ModuleAndAlgebra

variable (R A B M N : Type*)

/-
**Module.Finite.base_change** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [Add
CommMonoid M] [Module R M] [h : Module.Finite R M] : Module.Finite A (TensorProd
uct R A M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
instance Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
    [Module R M] [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by
  classical
    obtain ⟨s, hs⟩ := h.fg_top
    refine ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr ?_⟩⟩
    rintro x -
    induction x with
    | zero => exact zero_mem _
    | tmul x y =>
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs,
        Submodule.map_top, LinearMap.coe_range, ← mul_one x, ← smul_eq_mul,
        ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
/-
**Module.Finite.tensorProduct** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Finite.tensorProduct [CommSemiring R] [AddCommMonoid M] [Module R M
] [AddCommMonoid N] [Module R N] [hM : Module.Finite R M] [hN : Module.Finite R 
N] : Module.Finite R (TensorProduct R M N) where fg_top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `TensorProduct.map₂_mk_top_top_eq_top`：map₂_mk_top_top_eq_top : Submodule
.map₂ (mk R M N) ⊤ ⊤ = ⊤
· 使用定理 `Submodule.FG.map₂`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} {P : T
ype u_4} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommM
onoid N…
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
-/
instance Module.Finite.tensorProduct [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [hM : Module.Finite R M] [hN : Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) where
  fg_top := (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.fg_top.map₂ _ hN.fg_top)

end ModuleAndAlgebra

section NontrivialTensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/-
**Module.exists_isPrincipal_quotient_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.exists_isPrincipal_quotient_of_finite : exists N : Submodule R M, N
 != ⊤ ∧ Submodule.IsPrincipal (⊤ : Submodule R (M ⧸ N))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin`：exists_fin [Module.Finite R M] : exists (n : N
at) (s : Fin n -> M), span R (range s) = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsMin.Iio_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMin a → Se
t.Iio a = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.sSup_mem`：sSup_mem {s : Set Nat} (h₁ : s.Nonempty) (h₂ : BddAbove s)
 : sSup s in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `notMem_of_csSup_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattic
e α] {x : α} {s : Set α}, sSup s < x → BddAbove s → x ∉ s
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
（共 44 条，此处仅展示前 30 条）
-/
lemma Module.exists_isPrincipal_quotient_of_finite :
    ∃ N : Submodule R M, N ≠ ⊤ ∧ Submodule.IsPrincipal (⊤ : Submodule R (M ⧸ N)) := by
  obtain ⟨n, f, hf⟩ := @Module.Finite.exists_fin R M _ _ _ _
  let s := { m : ℕ | Submodule.span R (f '' Fin.val ⁻¹' Set.Iio m) ≠ ⊤ }
  have hns : ∀ x ∈ s, x < n := by
    refine fun x hx ↦ lt_iff_not_ge.mpr fun e ↦ ?_
    have : (Fin.val ⁻¹' Set.Iio x : Set (Fin n)) = Set.univ := by ext y; simpa using y.2.trans_le e
    simp [s, this, hf] at hx
  have hs₁ : s.Nonempty := ⟨0, by simp [s]⟩
  have hs₂ : BddAbove s := ⟨n, fun x hx ↦ (hns x hx).le⟩
  have hs := Nat.sSup_mem hs₁ hs₂
  refine ⟨_, hs, ⟨⟨Submodule.mkQ _ (f ⟨_, hns _ hs⟩), ?_⟩⟩⟩
  have := not_not.mp (notMem_of_csSup_lt (Order.lt_succ _) hs₂)
  rw [← Set.image_singleton, ← Submodule.map_span,
    ← (Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _)).eq_iff,
    Submodule.comap_map_eq, Submodule.ker_mkQ, Submodule.comap_top, ← this, ← Submodule.span_union,
    Order.Iio_succ_eq_insert (sSup s), ← Set.union_singleton, Set.preimage_union, Set.image_union,
    ← @Set.image_singleton _ _ f, Set.union_comm]
  congr!
  ext
  simp [Fin.ext_iff]
/-
**Module.exists_surjective_quotient_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.exists_surjective_quotient_of_finite : exists (I : Ideal R) (f : M 
->ₗ[R] R ⧸ I), I != ⊤ ∧ Function.Surjective f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.exists_isPrincipal_quotient_of_finite`：Module.exists_isPrincipal_
quotient_of_finite : exists N : Submodule R M, N != ⊤ ∧ Submodule.IsPrincipal (⊤
 : Submodule R (M ⧸ N))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.span_singleton_eq_range`：span_singleton_eq_range (x : M) : R ∙
 x = range (toSpanSingleton R M x)
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_top`：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 
0
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
lemma Module.exists_surjective_quotient_of_finite :
    ∃ (I : Ideal R) (f : M →ₗ[R] R ⧸ I), I ≠ ⊤ ∧ Function.Surjective f := by
  obtain ⟨N, hN, ⟨x, hx⟩⟩ := Module.exists_isPrincipal_quotient_of_finite R M
  let f := (LinearMap.toSpanSingleton R _ x).quotKerEquivOfSurjective
    (by rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hx])
  refine ⟨_, f.symm.toLinearMap.comp N.mkQ, fun e ↦ ?_, f.symm.surjective.comp N.mkQ_surjective⟩
  obtain rfl : x = 0 := by simpa using LinearMap.congr_fun (LinearMap.ker_eq_top.mp e) 1
  have : Nontrivial (M ⧸ N) := by rwa [Submodule.Quotient.nontrivial_iff]
  simp at hx

open TensorProduct
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (M ⊗[R] M) := by
  obtain ⟨I, ϕ, hI, hϕ⟩ := Module.exists_surjective_quotient_of_finite R M
  let ψ : M ⊗[R] M →ₗ[R] R ⧸ I :=
    (LinearMap.mul' R (R ⧸ I)).comp (TensorProduct.map ϕ ϕ)
  have : Nontrivial (R ⧸ I) := by rwa [Submodule.Quotient.nontrivial_iff]
  have : Function.Surjective ψ := by
    intro x; obtain ⟨x, rfl⟩ := hϕ x; obtain ⟨y, hy⟩ := hϕ 1; exact ⟨x ⊗ₜ y, by simp [ψ, hy]⟩
  exact this.nontrivial

end NontrivialTensorProduct

/-
**Subalgebra.finite_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.finite_sup {K L : Type*} [CommSemiring K] [CommSemiring L] [Alg
ebra K L] (E1 E2 : Subalgebra K L) [Module.Finite K E1] [Module.Finite K E2] : M
odule.Finite K ↥(E1 ⊔ E2)
参数：E1 E2 : Subalgebra K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.range_val`：range_val : S.val.range = S
· 使用定理 `Algebra.TensorProduct.productMap_range`：productMap_range : (productMap f
 g).range = f.range ⊔ g.range
-/
theorem Subalgebra.finite_sup {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
    (E1 E2 : Subalgebra K L) [Module.Finite K E1] [Module.Finite K E2] :
    Module.Finite K ↥(E1 ⊔ E2) := by
  rw [← E1.range_val, ← E2.range_val, ← Algebra.TensorProduct.productMap_range]
  exact Module.Finite.range (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap

-- Subsumed by `RingHom.Finite.tensorProductMap`.
/-
**RingHom.Finite.tensorProductMap_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma RingHom.Finite.tensorProductMap_id
    {R S S' T : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing S']
    [Algebra R S] [Algebra R T] [Algebra R S']
    {f : S →ₐ[R] S'} (Hf : f.Finite) :
    (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom.Finite := by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S S' := finite_algebraMap.mp Hf
  change (Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id R T)).Finite
  convert_to (((Algebra.TensorProduct.comm _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange R S S S' T)).toAlgHom.comp
    Algebra.TensorProduct.includeLeft).Finite
  · ext; simp
  exact (RingEquiv.finite _).comp (finite_algebraMap.mpr inferInstance)
/-
**RingHom.Finite.tensorProductMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.Finite.tensorProductMap {R S S' T T' : Type*} [CommRing R] [CommRi
ng S] [CommRing T] [CommRing S'] [CommRing T'] [Algebra R S] [Algebra R T] [Alge
bra R S'] [Algebra R T'] {f : S ->ₐ[R] S'} (Hf : f.Finite) {g : T ->ₐ[R] T'} (Hg
 : g.Finite) : (Algebra.TensorProduct.map f g).toRingHom.Finite
参数：Hf : f.Finite；Hg : g.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.map_comp_includeLeft`：map_comp_includeLeft (f : A 
->ₐ[S] C) (g : B ->ₐ[R] D) : (map f g).comp includeLeft = includeLeft.comp f
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.TensorProduct.map_restrictScalars_comp_includeRight`：map_restric
tScalars_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : ((map f g).restri
ctScalars R).comp includeRight = includeRight.com…
· 使用定理 `RingHom.Finite.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) 
(hf : f.Finite) : (g.comp f).Finite
· 使用定理 `_private.Mathlib.RingTheory.TensorProduct.Finite.0.RingHom.Finite.tensor
ProductMap_id`：∀ {R : Type u_1} {S : Type u_2} {S' : Type u_3} {T : Type u_4} [i
nst : CommRing R] [inst_1 : CommRing S]   [inst_2 : CommRing T] [inst_3 : C…
· 使用定理 `RingEquiv.finite`：∀ {A : Type u_1} {B : Type u_2} [inst : CommRing A] [i
nst_1 : CommRing B] (e : A ≃+* B), e.toRingHom.Finite
-/
lemma RingHom.Finite.tensorProductMap
    {R S S' T T' : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    {f : S →ₐ[R] S'} (Hf : f.Finite) {g : T →ₐ[R] T'} (Hg : g.Finite) :
    (Algebra.TensorProduct.map f g).toRingHom.Finite := by
  convert!
    RingHom.Finite.tensorProductMap_id (T := T') Hf |>.comp <|
      (Algebra.TensorProduct.comm _ _ _).toRingEquiv.finite |>.comp <|
        RingHom.Finite.tensorProductMap_id (T := S) Hg |>.comp <|
          (Algebra.TensorProduct.comm _ _ _).toRingEquiv.finite
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.comp_toRingHom]
  congr
  ext <;> simp
