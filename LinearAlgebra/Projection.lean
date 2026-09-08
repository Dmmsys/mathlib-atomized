/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Projection to a subspace

In this file we define
* `Submodule.projectionOnto (p q : Submodule R E) (h : IsCompl p q)`:
  the projection of a module `E` to a submodule `p` along its complement `q`;
  it is the unique linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.
* `Submodule.projection` (p q : Submodule R E) (h : IsCompl p q)`:
  the projection `Submodule.projectionOnto` as a linear map from `E` to `E`.
* `Submodule.isComplEquivProj p`: equivalence between submodules `q`
  such that `IsCompl p q` and projections `f : E → p`, `∀ x ∈ p, f x = x`.

We also provide some lemmas justifying correctness of our definitions.

## Tags

projection, complement subspace
-/

@[expose] public section

noncomputable section Ring

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]
variable {F : Type*} [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G]
variable (p q : Submodule R E)
variable {S : Type*} [Semiring S] {M : Type*} [AddCommMonoid M] [Module S M] (m : Submodule S M)

namespace LinearMap

variable {p}

open Submodule

/-
**LinearMap.ker_id_sub_eq_of_proj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_id_sub_eq_of_proj {f : E ->ₗ[R] p} (hf : forall x : p, f x = x) : ker 
(id - p.subtype.comp f) = p
参数：hf : forall x : p, f x = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem ker_id_sub_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) :
    ker (id - p.subtype.comp f) = p := by
  ext x
  simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero]
  exact ⟨fun h => h.symm ▸ Submodule.coe_mem _, fun hx => by rw [hf ⟨x, hx⟩, Subtype.coe_mk]⟩
/-
**LinearMap.range_eq_of_proj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_eq_of_proj {f : E ->ₗ[R] p} (hf : forall x : p, f x = x) : range f =
 ⊤
参数：hf : forall x : p, f x = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
-/
theorem range_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : range f = ⊤ :=
  range_eq_top.2 fun x => ⟨x, hf x⟩
/-
**LinearMap.isCompl_of_proj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isCompl_of_proj {f : E ->ₗ[R] p} (hf : forall x : p, f x = x) : IsCompl p 
(ker f)
参数：hf : forall x : p, f x = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.mk_eq_zero`：mk_eq_zero {x} (h : x in p) : (⟨x, h⟩ : p) = 0 ↔ x
 = 0
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `codisjoint_iff_le_sup`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_
1 : OrderTop α] {a b : α}, Codisjoint a b ↔ ⊤ ≤ a ⊔ b
· 使用定理 `Submodule.mem_sup'`：mem_sup' : x in p ⊔ p' ↔ exists (y : p) (z : p'), (y
 : M) + z = x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem isCompl_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : IsCompl p (ker f) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hpx, hfx⟩
    rw [SetLike.mem_coe, mem_ker, hf ⟨x, hpx⟩, mk_eq_zero] at hfx
    simp only [hfx, zero_mem]
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [mem_sup']
    refine ⟨f x, ⟨x - f x, ?_⟩, add_sub_cancel _ _⟩
    rw [mem_ker, map_sub, hf, sub_self]

end LinearMap

namespace Submodule

open LinearMap

/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. -/
/-
**Submodule.prodEquivOfIsCompl** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：prodEquivOfIsCompl (h : IsCompl p q) : (p × q) ≃ₗ[R] E
参数：h : IsCompl p q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `q` is a complement of `p`, then `p × q` is isomorphic to `E`.
-/
def prodEquivOfIsCompl (h : IsCompl p q) : (p × q) ≃ₗ[R] E := by
  apply LinearEquiv.ofBijective (p.subtype.coprod q.subtype)
  constructor
  · rw [← ker_eq_bot, ker_coprod_of_disjoint_range, ker_subtype, ker_subtype, prod_bot]
    rw [range_subtype, range_subtype]
    exact h.1
  · rw [← range_eq_top, ← sup_eq_range, h.sup_eq_top]

@[simp]
/-
**Submodule.coe_prodEquivOfIsCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_prodEquivOfIsCompl (h : IsCompl p q) : (prodEquivOfIsCompl p q h : p ×
 q ->ₗ[R] E) = p.subtype.coprod q.subtype
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodEquivOfIsCompl (h : IsCompl p q) :
    (prodEquivOfIsCompl p q h : p × q →ₗ[R] E) = p.subtype.coprod q.subtype := rfl

@[simp]
/-
**Submodule.coe_prodEquivOfIsCompl'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_prodEquivOfIsCompl' (h : IsCompl p q) (x : p × q) : prodEquivOfIsCompl
 p q h x = x.1 + x.2
参数：h : IsCompl p q；x : p × q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodEquivOfIsCompl' (h : IsCompl p q) (x : p × q) :
    prodEquivOfIsCompl p q h x = x.1 + x.2 := rfl
/-
**Submodule.prodEquivOfIsCompl_symm_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：prodEquivOfIsCompl_symm_apply_left (h : IsCompl p q) (x : p) : (prodEquivO
fIsCompl p q h).symm x = (x, 0)
参数：h : IsCompl p q；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodEquivOfIsCompl_symm_apply_left (h : IsCompl p q) (x : p) :
    (prodEquivOfIsCompl p q h).symm x = (x, 0) :=
  (prodEquivOfIsCompl p q h).symm_apply_eq.2 <| by simp
/-
**Submodule.prodEquivOfIsCompl_symm_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：prodEquivOfIsCompl_symm_apply_right (h : IsCompl p q) (x : q) : (prodEquiv
OfIsCompl p q h).symm x = (0, x)
参数：h : IsCompl p q；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodEquivOfIsCompl_symm_apply_right (h : IsCompl p q) (x : q) :
    (prodEquivOfIsCompl p q h).symm x = (0, x) :=
  (prodEquivOfIsCompl p q h).symm_apply_eq.2 <| by simp
/-
**Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
形式化陈述：prodEquivOfIsCompl_symm_apply_fst_eq_zero (h : IsCompl p q) {x : E} : ((pr
odEquivOfIsCompl p q h).symm x).1 = 0 ↔ x in q
参数：h : IsCompl p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Submodule.coe_prodEquivOfIsCompl'`：coe_prodEquivOfIsCompl' (h : IsCompl 
p q) (x : p × q) : prodEquivOfIsCompl p q h x = x.1 + x.2
· 使用定理 `Submodule.add_mem_iff_left`：∀ {R : Type u} {M : Type v} [inst : Ring R] 
[inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {
x y : M}, y ∈ p …
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Submodule.mem_right_iff_eq_zero_of_disjoint`：mem_right_iff_eq_zero_of_di
sjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p} : (x : M) in p' ↔ x = 
0
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prodEquivOfIsCompl_symm_apply_fst_eq_zero (h : IsCompl p q) {x : E} :
    ((prodEquivOfIsCompl p q h).symm x).1 = 0 ↔ x ∈ q := by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl', Submodule.add_mem_iff_left _ (Submodule.coe_mem _),
    mem_right_iff_eq_zero_of_disjoint h.disjoint]
/-
**Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
形式化陈述：prodEquivOfIsCompl_symm_apply_snd_eq_zero (h : IsCompl p q) {x : E} : ((pr
odEquivOfIsCompl p q h).symm x).2 = 0 ↔ x in p
参数：h : IsCompl p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Submodule.coe_prodEquivOfIsCompl'`：coe_prodEquivOfIsCompl' (h : IsCompl 
p q) (x : p × q) : prodEquivOfIsCompl p q h x = x.1 + x.2
· 使用定理 `Submodule.add_mem_iff_right`：∀ {R : Type u} {M : Type v} [inst : Ring R]
 [inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   
{x y : M}, x ∈ p …
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Submodule.mem_left_iff_eq_zero_of_disjoint`：mem_left_iff_eq_zero_of_disj
oint {p p' : Submodule R M} (h : Disjoint p p') {x : p'} : (x : M) in p ↔ x = 0
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prodEquivOfIsCompl_symm_apply_snd_eq_zero (h : IsCompl p q) {x : E} :
    ((prodEquivOfIsCompl p q h).symm x).2 = 0 ↔ x ∈ p := by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl', Submodule.add_mem_iff_right _ (Submodule.coe_mem _),
    mem_left_iff_eq_zero_of_disjoint h.disjoint]

@[simp]
/-
**Submodule.prodComm_trans_prodEquivOfIsCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：prodComm_trans_prodEquivOfIsCompl (h : IsCompl p q) : LinearEquiv.prodComm
 R q p ≪≫ₗ prodEquivOfIsCompl p q h = prodEquivOfIsCompl q p h.symm
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem prodComm_trans_prodEquivOfIsCompl (h : IsCompl p q) :
    LinearEquiv.prodComm R q p ≪≫ₗ prodEquivOfIsCompl p q h = prodEquivOfIsCompl q p h.symm :=
  LinearEquiv.ext fun _ => add_comm _ _

/-- Projection to a submodule along a complement. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.

For the projection from `E` to `E`, see `Submodule.projection`. See also:
* `Submodule.projectionOntoL` and `Submodule.projectionL` for the continuous versions.
* `Submodule.orthogonalProjection` and `Submodule.orthogonalProjectionOnto` for the projections
  along the orthogonal subspace.

See also `LinearMap.linearProjOfIsCompl`. -/
/-
**Submodule.projectionOnto** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：projectionOnto (h : IsCompl p q) : E ->ₗ[R] p
参数：h : IsCompl p q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection to a submodule along a complement. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`
.

For the projection from `E` to `E`, see `Submodule.projection`. See also:
* `Submodule.projectionOntoL` and `Submodule.projectionL` for the continuous ver
sions.
* `Submodule.orthogonalProjection` and `Submodule.orthogonalProjectionOnto` for 
the projections
  along the orthogonal subspace.

See also `LinearMap.linearProjOfIsCompl`.
-/
def projectionOnto (h : IsCompl p q) : E →ₗ[R] p :=
  LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm

/-- The linear projection onto a subspace along its complement
as a map from the full space to itself, as opposed to `Submodule.projectionOnto`,
which maps into the subtype.
This version is important as it satisfies `IsIdempotentElem`.

See also:
* `Submodule.projectionOntoL` and `Submodule.projectionL` for the continuous versions.
* `Submodule.orthogonalProjection` and `Submodule.orthogonalProjectionOnto` for the projections
  along the orthogonal subspace. -/
/-
**Submodule.projection** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：projection (hpq : IsCompl p q)
参数：hpq : IsCompl p q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear projection onto a subspace along its complement
as a map from the full space to itself, as opposed to `Submodule.projectionOnto`
,
which maps into the subtype.
This version is important as it satisfies `IsIdempotentElem`.

See also:
* `Submodule.projectionOntoL` and `Submodule.projectionL` for the continuous ver
sions.
* `Submodule.orthogonalProjection` and `Submodule.orthogonalProjectionOnto` for 
the projections
  along the orthogonal subspace.
-/
noncomputable def projection (hpq : IsCompl p q) :=
  p.subtype ∘ₗ p.projectionOnto q hpq

variable {p q}

open Submodule
/-
**Submodule.projection_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projection_apply (hpq : IsCompl p q) (x : E) : p.projection q hpq x = p.pr
ojectionOnto q hpq x
参数：hpq : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem projection_apply (hpq : IsCompl p q) (x : E) :
    p.projection q hpq x = p.projectionOnto q hpq x :=
  rfl

@[simp]
/-
**Submodule.coe_projectionOnto_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_projectionOnto_apply (hpq : IsCompl p q) (x : E) : (p.projectionOnto q
 hpq x : E) = p.projection q hpq x
参数：hpq : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_projectionOnto_apply (hpq : IsCompl p q) (x : E) :
    (p.projectionOnto q hpq x : E) = p.projection q hpq x :=
  rfl

@[simp]
/-
**Submodule.projection_apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projection_apply_mem (hpq : IsCompl p q) (x : E) : p.projection q hpq x in
 p
参数：hpq : IsCompl p q；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem projection_apply_mem (hpq : IsCompl p q) (x : E) :
    p.projection q hpq x ∈ p :=
  SetLike.coe_mem _

@[simp]
/-
**Submodule.projectionOnto_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionOnto_apply_left (h : IsCompl p q) (x : p) : projectionOnto p q h
 x = x
参数：h : IsCompl p q；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.prodEquivOfIsCompl_symm_apply_left`：prodEquivOfIsCompl_symm_ap
ply_left (h : IsCompl p q) (x : p) : (prodEquivOfIsCompl p q h).symm x = (x, 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projectionOnto_apply_left (h : IsCompl p q) (x : p) :
    projectionOnto p q h x = x := by
  simp [projectionOnto, prodEquivOfIsCompl_symm_apply_left]

@[simp]
/-
**Submodule.projection_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projection_apply_left (hpq : IsCompl p q) (x : p) : p.projection q hpq x =
 x
参数：hpq : IsCompl p q；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projection_apply_left (hpq : IsCompl p q) (x : p) :
    p.projection q hpq x = x := by simp [projection]
/-
**Submodule.projectionOnto_apply_of_mem_left** 是 Mathlib 中的一个引理，位于命名空间 `Submodul
e`。
形式化陈述：projectionOnto_apply_of_mem_left (hpq : IsCompl p q) {x : E} (hx : x in p)
 : p.projectionOnto q hpq x = ⟨x, hx⟩
参数：hpq : IsCompl p q；hx : x in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
-/
lemma projectionOnto_apply_of_mem_left (hpq : IsCompl p q) {x : E} (hx : x ∈ p) :
    p.projectionOnto q hpq x = ⟨x, hx⟩ := projectionOnto_apply_left hpq ⟨x, hx⟩
/-
**Submodule.projection_apply_of_mem_left** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：projection_apply_of_mem_left (hpq : IsCompl p q) {x : E} (hx : x in p) : p
.projection q hpq x = x
参数：hpq : IsCompl p q；hx : x in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projection_apply_left`：projection_apply_left (hpq : IsCompl p 
q) (x : p) : p.projection q hpq x = x
-/
lemma projection_apply_of_mem_left (hpq : IsCompl p q) {x : E} (hx : x ∈ p) :
    p.projection q hpq x = x := projection_apply_left hpq ⟨x, hx⟩

@[simp]
/-
**Submodule.range_projectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_projectionOnto (h : IsCompl p q) : range (projectionOnto p q h) = ⊤
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_eq_of_proj`：range_eq_of_proj {f : E ->ₗ[R] p} (hf : fora
ll x : p, f x = x) : range f = ⊤
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
-/
theorem range_projectionOnto (h : IsCompl p q) : range (projectionOnto p q h) = ⊤ :=
  range_eq_of_proj (projectionOnto_apply_left h)

@[simp]
/-
**Submodule.range_projection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_projection (hpq : IsCompl p q) : range (p.projection q hpq) = p
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.range_projectionOnto`：range_projectionOnto (h : IsCompl p q) :
 range (projectionOnto p q h) = ⊤
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_projection (hpq : IsCompl p q) : range (p.projection q hpq) = p := by
  simp [projection, range_comp]
/-
**Submodule.projectionOnto_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionOnto_surjective (h : IsCompl p q) : Function.Surjective (project
ionOnto p q h)
参数：h : IsCompl p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.range_projectionOnto`：range_projectionOnto (h : IsCompl p q) :
 range (projectionOnto p q h) = ⊤
-/
theorem projectionOnto_surjective (h : IsCompl p q) :
    Function.Surjective (projectionOnto p q h) :=
  range_eq_top.mp (range_projectionOnto h)

@[simp]
/-
**Submodule.projectionOnto_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：projectionOnto_apply_eq_zero_iff (h : IsCompl p q) {x : E} : projectionOnt
o p q h x = 0 ↔ x in q
参数：h : IsCompl p q。
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
theorem projectionOnto_apply_eq_zero_iff (h : IsCompl p q) {x : E} :
    projectionOnto p q h x = 0 ↔ x ∈ q := by
  simp [projectionOnto, prodEquivOfIsCompl_symm_apply_fst_eq_zero]

@[simp]
/-
**Submodule.projection_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projection_apply_eq_zero_iff (hpq : IsCompl p q) {x : E} : p.projection q 
hpq x = 0 ↔ x in q
参数：hpq : IsCompl p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem projection_apply_eq_zero_iff (hpq : IsCompl p q) {x : E} :
    p.projection q hpq x = 0 ↔ x ∈ q := by
  simp [projection, -coe_projectionOnto_apply]

alias ⟨_, projectionOnto_apply_of_mem_right⟩ :=
  projectionOnto_apply_eq_zero_iff

alias ⟨_, projection_apply_of_mem_right⟩ :=
  projection_apply_eq_zero_iff

@[simp]
/-
**Submodule.projectionOnto_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionOnto_apply_right (h : IsCompl p q) (x : q) : projectionOnto p q 
h x = 0
参数：h : IsCompl p q；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionOnto_apply_of_mem_right`：∀ {R : Type u_1} [inst : Ri
ng R] {E : Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   {p
 q : Submodule R E} (h : IsCompl …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem projectionOnto_apply_right (h : IsCompl p q) (x : q) :
    projectionOnto p q h x = 0 :=
  projectionOnto_apply_of_mem_right h x.2

@[simp]
/-
**Submodule.projection_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projection_apply_right (h : IsCompl p q) (x : q) : p.projection q h x = 0
参数：h : IsCompl p q；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projection_apply_of_mem_right`：∀ {R : Type u_1} [inst : Ring R
] {E : Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   {p q :
 Submodule R E} (hpq : IsComp…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem projection_apply_right (h : IsCompl p q) (x : q) :
    p.projection q h x = 0 :=
  projection_apply_of_mem_right h x.2

@[simp]
/-
**Submodule.ker_projectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_projectionOnto (h : IsCompl p q) : ker (projectionOnto p q h) = q
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Submodule.projectionOnto_apply_eq_zero_iff`：projectionOnto_apply_eq_zero
_iff (h : IsCompl p q) {x : E} : projectionOnto p q h x = 0 ↔ x in q
-/
theorem ker_projectionOnto (h : IsCompl p q) : ker (projectionOnto p q h) = q :=
  ext fun _ => mem_ker.trans (projectionOnto_apply_eq_zero_iff h)

@[simp]
/-
**Submodule.ker_projection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_projection (hpq : IsCompl p q) : ker (p.projection q hpq) = q
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `Submodule.ker_projectionOnto`：ker_projectionOnto (h : IsCompl p q) : ker
 (projectionOnto p q h) = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_projection (hpq : IsCompl p q) :
    ker (p.projection q hpq) = q := by
  simp [projection, ker_comp]
/-
**Submodule.projectionOnto_comp_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionOnto_comp_subtype (h : IsCompl p q) : (projectionOnto p q h).com
p p.subtype = LinearMap.id
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
-/
theorem projectionOnto_comp_subtype (h : IsCompl p q) :
    (projectionOnto p q h).comp p.subtype = LinearMap.id :=
  LinearMap.ext <| projectionOnto_apply_left h
/-
**Submodule.projectionOnto_projection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionOnto_projection (h : IsCompl p q) (x : E) : projectionOnto p q h
 (p.projection q h x) = projectionOnto p q h x
参数：h : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
-/
theorem projectionOnto_projection (h : IsCompl p q) (x : E) :
    projectionOnto p q h (p.projection q h x) = projectionOnto p q h x :=
  projectionOnto_apply_left h _

/-- The linear projection onto a subspace along its complement is an idempotent. -/
@[simp]
/-
**Submodule.isIdempotentElem_projection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isIdempotentElem_projection (hpq : IsCompl p q) : IsIdempotentElem (p.proj
ection q hpq)
参数：hpq : IsCompl p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.projectionOnto_projection`：projectionOnto_projection (h : IsCo
mpl p q) (x : E) : projectionOnto p q h (p.projection q h x) = projectionOnto p 
q h x

--- 原说明 ---
The linear projection onto a subspace along its complement is an idempotent.
-/
theorem isIdempotentElem_projection (hpq : IsCompl p q) :
    IsIdempotentElem (p.projection q hpq) :=
  LinearMap.ext fun _ ↦ congr($(projectionOnto_projection hpq _))
/-
**Submodule.existsUnique_add_of_isCompl_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：existsUnique_add_of_isCompl_prod (hc : IsCompl p q) (x : E) : exists! u : 
p × q, (u.fst : E) + u.snd = x
参数：hc : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.existsUnique`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Bijective f → ∀ (b : β), ∃! a, f a = b
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem existsUnique_add_of_isCompl_prod (hc : IsCompl p q) (x : E) :
    ∃! u : p × q, (u.fst : E) + u.snd = x :=
  (prodEquivOfIsCompl _ _ hc).toEquiv.bijective.existsUnique _
/-
**Submodule.existsUnique_add_of_isCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：existsUnique_add_of_isCompl (hc : IsCompl p q) (x : E) : exists (u : p) (v
 : q), (u : E) + v = x ∧ forall (r : p) (s : q), (r : E) + s = x -> r = u ∧ s = 
v
参数：hc : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.existsUnique_add_of_isCompl_prod`：existsUnique_add_of_isCompl_
prod (hc : IsCompl p q) (x : E) : exists! u : p × q, (u.fst : E) + u.snd = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.eq_iff_fst_eq_snd_eq`：∀ {α : Type u_1} {β : Type u_2} {p q : α × β}
, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
-/
theorem existsUnique_add_of_isCompl (hc : IsCompl p q) (x : E) :
    ∃ (u : p) (v : q), (u : E) + v = x ∧ ∀ (r : p) (s : q), (r : E) + s = x → r = u ∧ s = v :=
  let ⟨u, hu₁, hu₂⟩ := existsUnique_add_of_isCompl_prod hc x
  ⟨u.1, u.2, hu₁, fun r s hrs => Prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩
/-
**Submodule.projection_add_projection_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：projection_add_projection_eq_self (hpq : IsCompl p q) (x : E) : (p.project
ion q hpq) x + (q.projection p hpq.symm) x = x
参数：hpq : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.prodComm_trans_prodEquivOfIsCompl`：prodComm_trans_prodEquivOfI
sCompl (h : IsCompl p q) : LinearEquiv.prodComm R q p ≪≫ₗ prodEquivOfIsCompl p q
 h = prodEquivOfIsCompl q p h.sym…
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem projection_add_projection_eq_self (hpq : IsCompl p q) (x : E) :
    (p.projection q hpq) x + (q.projection p hpq.symm) x = x := by
  dsimp only [projection, projectionOnto]
  rw [← prodComm_trans_prodEquivOfIsCompl _ _ hpq]
  exact (prodEquivOfIsCompl _ _ hpq).apply_symm_apply x
/-
**Submodule.projection_add_projection_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：projection_add_projection_eq_id (hpq : IsCompl p q) : p.projection q hpq +
 q.projection p hpq.symm = .id
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Submodule.projection_add_projection_eq_self`：projection_add_projection_e
q_self (hpq : IsCompl p q) (x : E) : (p.projection q hpq) x + (q.projection p hp
q.symm) x = x
-/
theorem projection_add_projection_eq_id (hpq : IsCompl p q) :
    p.projection q hpq + q.projection p hpq.symm = .id :=
  LinearMap.ext (projection_add_projection_eq_self hpq)
/-
**Submodule.projection_eq_self_sub_projection** 是 Mathlib 中的一个引理，位于命名空间 `Submodu
le`。
形式化陈述：projection_eq_self_sub_projection (hpq : IsCompl p q) (x : E) : q.projecti
on p hpq.symm x = x - p.projection q hpq x
参数：hpq : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Submodule.projection_add_projection_eq_self`：projection_add_projection_e
q_self (hpq : IsCompl p q) (x : E) : (p.projection q hpq) x + (q.projection p hp
q.symm) x = x
-/
lemma projection_eq_self_sub_projection (hpq : IsCompl p q) (x : E) :
    q.projection p hpq.symm x = x - p.projection q hpq x := by
  rw [eq_sub_iff_add_eq, projection_add_projection_eq_self]
/-
**Submodule.projection_eq_id_sub_projection** 是 Mathlib 中的一个引理，位于命名空间 `Submodule
`。
形式化陈述：projection_eq_id_sub_projection (hpq : IsCompl p q) : q.projection p hpq.s
ymm = .id - p.projection q hpq
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用引理 `Submodule.projection_eq_self_sub_projection`：projection_eq_self_sub_proj
ection (hpq : IsCompl p q) (x : E) : q.projection p hpq.symm x = x - p.projectio
n q hpq x
-/
lemma projection_eq_id_sub_projection (hpq : IsCompl p q) :
    q.projection p hpq.symm = .id - p.projection q hpq :=
  LinearMap.ext (projection_eq_self_sub_projection hpq)

/-- The projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p`. -/
/-
**Submodule.projection_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {E : Type u_2} [inst_1 : AddCommGroup E] 
[inst_2 : _root_.Module R E]   {p q : Submodule R E} (hpq : IsCompl p q) (x : E)
, (p.projection q hpq) x = x ↔ x ∈ p
参数：hpq : IsCompl p q；x : E；p.projection q hpq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用引理 `Submodule.projection_eq_self_sub_projection`：projection_eq_self_sub_proj
ection (hpq : IsCompl p q) (x : E) : q.projection p hpq.symm x = x - p.projectio
n q hpq x
· 使用定理 `Submodule.projection_apply_eq_zero_iff`：projection_apply_eq_zero_iff (hp
q : IsCompl p q) {x : E} : p.projection q hpq x = 0 ↔ x in q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p`.
-/
@[simp] lemma projection_eq_self_iff (hpq : IsCompl p q) (x : E) :
    p.projection q hpq x = x ↔ x ∈ p := by
  rw [eq_comm, ← sub_eq_zero, ← projection_eq_self_sub_projection, projection_apply_eq_zero_iff]

@[simp]
/-
**Submodule.prodEquivOfIsCompl_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prodEquivOfIsCompl_symm_apply (hpq : IsCompl p q) (x : E) : (p.prodEquivOf
IsCompl q hpq).symm x = (p.projectionOnto q hpq x, q.projectionOnto p hpq.symm x
)
参数：hpq : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.prodComm_trans_prodEquivOfIsCompl`：prodComm_trans_prodEquivOfI
sCompl (h : IsCompl p q) : LinearEquiv.prodComm R q p ≪≫ₗ prodEquivOfIsCompl p q
 h = prodEquivOfIsCompl q p h.sym…
-/
theorem prodEquivOfIsCompl_symm_apply (hpq : IsCompl p q) (x : E) :
    (p.prodEquivOfIsCompl q hpq).symm x =
      (p.projectionOnto q hpq x, q.projectionOnto p hpq.symm x) :=
  Prod.ext rfl congr(($(prodComm_trans_prodEquivOfIsCompl p q hpq).symm x).1)

@[simp]
/-
**Submodule.toLinearMap_prodEquivOfIsCompl_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：toLinearMap_prodEquivOfIsCompl_symm (hpq : IsCompl p q) : (p.prodEquivOfIs
Compl q hpq).symm.toLinearMap = (p.projectionOnto q hpq).prod (q.projectionOnto 
p hpq.symm)
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.prodEquivOfIsCompl_symm_apply`：prodEquivOfIsCompl_symm_apply (
hpq : IsCompl p q) (x : E) : (p.prodEquivOfIsCompl q hpq).symm x = (p.projection
Onto q hpq x, q.projectionOnt…
· 使用定理 `LinearMap.prod_apply`：∀ {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Ty
pe y} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M
₂] [inst_3…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem toLinearMap_prodEquivOfIsCompl_symm (hpq : IsCompl p q) :
    (p.prodEquivOfIsCompl q hpq).symm.toLinearMap =
      (p.projectionOnto q hpq).prod (q.projectionOnto p hpq.symm) :=
  LinearMap.ext <| by simp
/-
**Submodule.sub_projection_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sub_projection_mem (h : IsCompl p q) (x : E) : x - p.projection q h x in q
参数：h : IsCompl p q；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.projection_eq_self_sub_projection`：projection_eq_self_sub_proj
ection (hpq : IsCompl p q) (x : E) : q.projection p hpq.symm x = x - p.projectio
n q hpq x
· 使用定理 `Submodule.projection_apply_mem`：projection_apply_mem (hpq : IsCompl p q)
 (x : E) : p.projection q hpq x in p
-/
theorem sub_projection_mem (h : IsCompl p q) (x : E) : x - p.projection q h x ∈ q := by
  rw [← projection_eq_self_sub_projection h]
  exact projection_apply_mem h.symm x

variable (p q) in
/-- If `q` is a complement of `p`, then `M ⧸ p ≃ q`. The forward direction sends a quotient class
to its projection onto `q` along `p`; the backward direction sends an element of `q` to its class
in `M ⧸ p`. -/
@[simps! symm_apply]
/-
**Submodule.quotientEquivOfIsCompl** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientEquivOfIsCompl (h : IsCompl p q) : (E ⧸ p) ≃ₗ[R] q
参数：h : IsCompl p q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `q` is a complement of `p`, then `M ⧸ p ≃ q`. The forward direction sends a q
uotient class
to its projection onto `q` along `p`; the backward direction sends an element of
 `q` to its class
in `M ⧸ p`.
-/
def quotientEquivOfIsCompl (h : IsCompl p q) : (E ⧸ p) ≃ₗ[R] q :=
  .ofLinearMap
    (p.liftQ (q.projectionOnto p h.symm) (by simp))
    (p.mkQ ∘ₗ q.subtype)
    (by ext; simp)
    (by ext; simp [Quotient.eq, sub_mem_comm_iff, sub_projection_mem])
/-
**Submodule.quotientEquivOfIsCompl_comp_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：quotientEquivOfIsCompl_comp_mkQ (h : IsCompl p q) : (quotientEquivOfIsComp
l p q h : E ⧸ p ->ₗ[R] q) ∘ₗ p.mkQ = q.projectionOnto p h.symm
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientEquivOfIsCompl_comp_mkQ (h : IsCompl p q) :
    (quotientEquivOfIsCompl p q h : E ⧸ p →ₗ[R] q) ∘ₗ p.mkQ = q.projectionOnto p h.symm :=
  rfl

@[simp]
/-
**Submodule.quotientEquivOfIsCompl_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：quotientEquivOfIsCompl_apply_mk (h : IsCompl p q) (x : E) : quotientEquivO
fIsCompl p q h (Quotient.mk x) = q.projectionOnto p h.symm x
参数：h : IsCompl p q；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientEquivOfIsCompl_apply_mk (h : IsCompl p q) (x : E) :
    quotientEquivOfIsCompl p q h (Quotient.mk x) = q.projectionOnto p h.symm x :=
  rfl
/-
**Submodule.quotientEquivOfIsCompl_apply_mk_right** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：quotientEquivOfIsCompl_apply_mk_right (h : IsCompl p q) (x : q) : quotient
EquivOfIsCompl p q h (Quotient.mk x) = x
参数：h : IsCompl p q；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem quotientEquivOfIsCompl_apply_mk_right (h : IsCompl p q) (x : q) :
    quotientEquivOfIsCompl p q h (Quotient.mk x) = x :=
  (quotientEquivOfIsCompl p q h).apply_symm_apply x

@[deprecated (since := "2026-05-06")]
alias quotientEquivOfIsCompl_apply_mk_coe := quotientEquivOfIsCompl_apply_mk_right

@[simp]
/-
**Submodule.mk_quotientEquivOfIsCompl_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：mk_quotientEquivOfIsCompl_apply (h : IsCompl p q) (x : E ⧸ p) : (Quotient.
mk (quotientEquivOfIsCompl p q h x) : E ⧸ p) = x
参数：h : IsCompl p q；x : E ⧸ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem mk_quotientEquivOfIsCompl_apply (h : IsCompl p q) (x : E ⧸ p) :
    (Quotient.mk (quotientEquivOfIsCompl p q h x) : E ⧸ p) = x :=
  (quotientEquivOfIsCompl p q h).symm_apply_apply x

@[simp]
/-
**Submodule.toLinearMap_quotientEquivOfIsCompl** 是 Mathlib 中的一个引理，位于命名空间 `Submod
ule`。
形式化陈述：toLinearMap_quotientEquivOfIsCompl (h : IsCompl p q) : (p.quotientEquivOfI
sCompl q h).toLinearMap = p.liftQ (q.projectionOnto p h.symm) (by simp)
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_quotientEquivOfIsCompl (h : IsCompl p q) :
    (p.quotientEquivOfIsCompl q h).toLinearMap = p.liftQ (q.projectionOnto p h.symm) (by simp) :=
  rfl

@[simp]
/-
**Submodule.toLinearMap_symm_quotientEquivOfIsCompl** 是 Mathlib 中的一个引理，位于命名空间 `S
ubmodule`。
形式化陈述：toLinearMap_symm_quotientEquivOfIsCompl (h : IsCompl p q) : (p.quotientEqu
ivOfIsCompl q h).symm.toLinearMap = p.mkQ ∘ₗ q.subtype
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_symm_quotientEquivOfIsCompl (h : IsCompl p q) :
    (p.quotientEquivOfIsCompl q h).symm.toLinearMap = p.mkQ ∘ₗ q.subtype :=
  rfl

end Submodule

namespace LinearMap

open Submodule

section

/-- Projection to the image of an injection along a complement.

This has an advantage over `Submodule.projectionOnto` in that it allows the user better
definitional control over the type. -/
/-
**LinearMap.linearProjOfIsCompl** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：linearProjOfIsCompl {F : Type*} [AddCommGroup F] [Module R F] (i : F ->ₗ[R
] E) (hi : Function.Injective i) (h : IsCompl (LinearMap.range i) q) : E ->ₗ[R] 
F
参数：i : F ->ₗ[R] E；hi : Function.Injective i；h : IsCompl (LinearMap.range i) q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection to the image of an injection along a complement.

This has an advantage over `Submodule.projectionOnto` in that it allows the user
 better
definitional control over the type.
-/
def linearProjOfIsCompl {F : Type*} [AddCommGroup F] [Module R F]
    (i : F →ₗ[R] E) (hi : Function.Injective i)
    (h : IsCompl (LinearMap.range i) q) : E →ₗ[R] F :=
  (LinearEquiv.ofInjective i hi).symm ∘ₗ (LinearMap.range i).projectionOnto q h

variable {F : Type*} [AddCommGroup F] [Module R F] (i : F →ₗ[R] E) (hi : Function.Injective i)
    (h : IsCompl (LinearMap.range i) q)

@[simp]
/-
**LinearMap.linearProjOfIsCompl_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：linearProjOfIsCompl_apply_left (x : F) : linearProjOfIsCompl q i hi h (i x
) = x
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearEquiv.ofInjective_symm_apply`：ofInjective_symm_apply [RingHomInvPa
ir σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f} (x : LinearMap.range f) :
 f ((ofInjective f h).sy…
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearProjOfIsCompl_apply_left (x : F) : linearProjOfIsCompl q i hi h (i x) = x := by
  obtain ⟨ix, rfl⟩ := (LinearEquiv.ofInjective i hi).symm.surjective x
  simp [linearProjOfIsCompl]
/-
**LinearMap.linearProjOfIsCompl_apply_right'** 是 Mathlib 中的一个引理，位于命名空间 `LinearMa
p`。
形式化陈述：linearProjOfIsCompl_apply_right' (x : E) (hx : x in q) : linearProjOfIsCom
pl q i hi h x = 0
参数：x : E；hx : x in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
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
-/
lemma linearProjOfIsCompl_apply_right' (x : E) (hx : x ∈ q) :
    linearProjOfIsCompl q i hi h x = 0 := by
  simpa [LinearMap.linearProjOfIsCompl]

@[simp]
/-
**LinearMap.linearProjOfIsCompl_apply_right** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
形式化陈述：linearProjOfIsCompl_apply_right (x : q) : linearProjOfIsCompl q i hi h x =
 0
参数：x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.projectionOnto_apply_right`：projectionOnto_apply_right (h : Is
Compl p q) (x : q) : projectionOnto p q h x = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearProjOfIsCompl_apply_right (x : q) : linearProjOfIsCompl q i hi h x = 0 := by
  simp [LinearMap.linearProjOfIsCompl]

@[simp]
/-
**LinearMap.ker_linearProjOfIsCompl** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ker_linearProjOfIsCompl : ker (linearProjOfIsCompl q i hi h) = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.ker_comp`：ker_comp (l : M ->ₛₗ[σ₁₂] M₂) : LinearMap.ker (((e
'' : M₂ ->ₛₗ[σ₂₃] M₃).comp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.ker
 l
· 使用定理 `Submodule.ker_projectionOnto`：ker_projectionOnto (h : IsCompl p q) : ker
 (projectionOnto p q h) = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ker_linearProjOfIsCompl : ker (linearProjOfIsCompl q i hi h) = q := by
  simp [LinearMap.linearProjOfIsCompl]

end

/-- Given linear maps `φ` and `ψ` from complement submodules, `LinearMap.ofIsCompl` is
the induced linear map over the entire module. -/
/-
**LinearMap.ofIsCompl** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl {p q : Submodule R E} (h : IsCompl p q) (φ : p ->ₗ[R] F) (ψ : q 
->ₗ[R] F) : E ->ₗ[R] F
参数：h : IsCompl p q；φ : p ->ₗ[R] F；ψ : q ->ₗ[R] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given linear maps `φ` and `ψ` from complement submodules, `LinearMap.ofIsCompl` 
is
the induced linear map over the entire module.
-/
def ofIsCompl {p q : Submodule R E} (h : IsCompl p q) (φ : p →ₗ[R] F) (ψ : q →ₗ[R] F) : E →ₗ[R] F :=
  LinearMap.coprod φ ψ ∘ₗ ↑(Submodule.prodEquivOfIsCompl _ _ h).symm

variable {p q}

@[simp]
/-
**LinearMap.ofIsCompl_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_apply_left (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (
u : p) : ofIsCompl h φ ψ (u : E) = φ u
参数：h : IsCompl p q；u : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Submodule.toLinearMap_prodEquivOfIsCompl_symm`：toLinearMap_prodEquivOfIs
Compl_symm (hpq : IsCompl p q) : (p.prodEquivOfIsCompl q hpq).symm.toLinearMap =
 (p.projectionOnto q hpq).prod (q.p…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `Submodule.projectionOnto_apply_right`：projectionOnto_apply_right (h : Is
Compl p q) (x : q) : projectionOnto p q h x = 0
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsCompl_apply_left (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (u : p) :
    ofIsCompl h φ ψ (u : E) = φ u := by simp [ofIsCompl]

@[simp]
/-
**LinearMap.ofIsCompl_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_apply_right (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} 
(v : q) : ofIsCompl h φ ψ (v : E) = ψ v
参数：h : IsCompl p q；v : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Submodule.toLinearMap_prodEquivOfIsCompl_symm`：toLinearMap_prodEquivOfIs
Compl_symm (hpq : IsCompl p q) : (p.prodEquivOfIsCompl q hpq).symm.toLinearMap =
 (p.projectionOnto q hpq).prod (q.p…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.projectionOnto_apply_right`：projectionOnto_apply_right (h : Is
Compl p q) (x : q) : projectionOnto p q h x = 0
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
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsCompl_apply_right (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (v : q) :
    ofIsCompl h φ ψ (v : E) = ψ v := by simp [ofIsCompl]
/-
**LinearMap.ofIsCompl_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_eq (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} {χ : E ->
ₗ[R] F} (hφ : forall u, φ u = χ u) (hψ : forall u, ψ u = χ u) : ofIsCompl h φ ψ 
= χ
参数：h : IsCompl p q；hφ : forall u, φ u = χ u；hψ : forall u, ψ u = χ u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.existsUnique_add_of_isCompl`：existsUnique_add_of_isCompl (hc :
 IsCompl p q) (x : E) : exists (u : p) (v : q), (u : E) + v = x ∧ forall (r : p)
 (s : q), (r : E) + s = x -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Submodule.toLinearMap_prodEquivOfIsCompl_symm`：toLinearMap_prodEquivOfIs
Compl_symm (hpq : IsCompl p q) : (p.prodEquivOfIsCompl q hpq).symm.toLinearMap =
 (p.projectionOnto q hpq).prod (q.p…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `Submodule.projectionOnto_apply_right`：projectionOnto_apply_right (h : Is
Compl p q) (x : q) : projectionOnto p q h x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsCompl_eq (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F}
    (hφ : ∀ u, φ u = χ u) (hψ : ∀ u, ψ u = χ u) : ofIsCompl h φ ψ = χ := by
  ext x
  obtain ⟨_, _, rfl, _⟩ := existsUnique_add_of_isCompl h x
  simp [ofIsCompl, hφ, hψ]
/-
**LinearMap.ofIsCompl_eq'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_eq' (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} {χ : E -
>ₗ[R] F} (hφ : φ = χ.comp p.subtype) (hψ : ψ = χ.comp q.subtype) : ofIsCompl h φ
 ψ = χ
参数：h : IsCompl p q；hφ : φ = χ.comp p.subtype；hψ : ψ = χ.comp q.subtype。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ofIsCompl_eq`：ofIsCompl_eq (h : IsCompl p q) {φ : p ->ₗ[R] F} 
{ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F} (hφ : forall u, φ u = χ u) (hψ : forall u, ψ u
 = χ u) : of…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ofIsCompl_eq' (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F}
    (hφ : φ = χ.comp p.subtype) (hψ : ψ = χ.comp q.subtype) : ofIsCompl h φ ψ = χ :=
  ofIsCompl_eq h (fun _ => hφ.symm ▸ rfl) fun _ => hψ.symm ▸ rfl
/-
**LinearMap.ofIsCompl_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_eq_add (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} : o
fIsCompl hpq φ ψ = (φ ∘ₗ p.projectionOnto q hpq) + (ψ ∘ₗ q.projectionOnto p hpq.
symm)
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Submodule.existsUnique_add_of_isCompl`：existsUnique_add_of_isCompl (hc :
 IsCompl p q) (x : E) : exists (u : p) (v : q), (u : E) + v = x ∧ forall (r : p)
 (s : q), (r : E) + s = x -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.ofIsCompl_apply_left`：ofIsCompl_apply_left (h : IsCompl p q) {
φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (u : p) : ofIsCompl h φ ψ (u : E) = φ u
· 使用定理 `LinearMap.ofIsCompl_apply_right`：ofIsCompl_apply_right (h : IsCompl p q)
 {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (v : q) : ofIsCompl h φ ψ (v : E) = ψ v
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `Submodule.projectionOnto_apply_right`：projectionOnto_apply_right (h : Is
Compl p q) (x : q) : projectionOnto p q h x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsCompl_eq_add (hpq : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} :
    ofIsCompl hpq φ ψ = (φ ∘ₗ p.projectionOnto q hpq) + (ψ ∘ₗ q.projectionOnto p hpq.symm) := by
  ext x
  obtain ⟨a, b, rfl, _⟩ := existsUnique_add_of_isCompl hpq x
  simp

@[simp]
/-
**LinearMap.ofIsCompl_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_zero (h : IsCompl p q) : (ofIsCompl h 0 0 : E ->ₗ[R] F) = 0
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ofIsCompl_eq`：ofIsCompl_eq (h : IsCompl p q) {φ : p ->ₗ[R] F} 
{ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F} (hφ : forall u, φ u = χ u) (hψ : forall u, ψ u
 = χ u) : of…
-/
theorem ofIsCompl_zero (h : IsCompl p q) : (ofIsCompl h 0 0 : E →ₗ[R] F) = 0 :=
  ofIsCompl_eq _ (fun _ => rfl) fun _ => rfl

@[simp]
/-
**LinearMap.ofIsCompl_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_add (h : IsCompl p q) {φ₁ φ₂ : p ->ₗ[R] F} {ψ₁ ψ₂ : q ->ₗ[R] F} 
: ofIsCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsCompl h φ₁ ψ₁ + ofIsCompl h φ₂ ψ₂
参数：h : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ofIsCompl_eq`：ofIsCompl_eq (h : IsCompl p q) {φ : p ->ₗ[R] F} 
{ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F} (hφ : forall u, φ u = χ u) (hψ : forall u, ψ u
 = χ u) : of…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.ofIsCompl_apply_left`：ofIsCompl_apply_left (h : IsCompl p q) {
φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (u : p) : ofIsCompl h φ ψ (u : E) = φ u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearMap.ofIsCompl_apply_right`：ofIsCompl_apply_right (h : IsCompl p q)
 {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (v : q) : ofIsCompl h φ ψ (v : E) = ψ v
-/
theorem ofIsCompl_add (h : IsCompl p q) {φ₁ φ₂ : p →ₗ[R] F} {ψ₁ ψ₂ : q →ₗ[R] F} :
    ofIsCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsCompl h φ₁ ψ₁ + ofIsCompl h φ₂ ψ₂ :=
  ofIsCompl_eq _ (by simp) (by simp)

@[simp]
/-
**LinearMap.ofIsCompl_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_smul {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Modu
le R E] {F : Type*} [AddCommGroup F] [Module R F] {p q : Submodule R E} (h : IsC
ompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (c : R) : ofIsCompl h (c • φ) (c • ψ
) = c • ofIsCompl h φ ψ
参数：h : IsCompl p q；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ofIsCompl_eq`：ofIsCompl_eq (h : IsCompl p q) {φ : p ->ₗ[R] F} 
{ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F} (hφ : forall u, φ u = χ u) (hψ : forall u, ψ u
 = χ u) : of…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ofIsCompl_apply_left`：ofIsCompl_apply_left (h : IsCompl p q) {
φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (u : p) : ofIsCompl h φ ψ (u : E) = φ u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearMap.ofIsCompl_apply_right`：ofIsCompl_apply_right (h : IsCompl p q)
 {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (v : q) : ofIsCompl h φ ψ (v : E) = ψ v
-/
theorem ofIsCompl_smul {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F] {p q : Submodule R E} (h : IsCompl p q)
    {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (c : R) : ofIsCompl h (c • φ) (c • ψ) = c • ofIsCompl h φ ψ :=
  ofIsCompl_eq _ (by simp) (by simp)
/-
**LinearMap.surjective_comp_projectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：surjective_comp_projectionOnto (h : IsCompl p q) [Module R M] : Function.S
urjective (comp (p.projectionOnto q h) : (M ->ₗ[R] E) -> _)
参数：h : IsCompl p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surjective_comp_projectionOnto (h : IsCompl p q) [Module R M] :
    Function.Surjective (comp (p.projectionOnto q h) : (M →ₗ[R] E) → _) :=
  fun f ↦ ⟨p.subtype ∘ₗ f, by ext; simp⟩
/-
**LinearMap.surjective_comp_subtype_of_isComplemented** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap`。
形式化陈述：surjective_comp_subtype_of_isComplemented (h : IsComplemented p) [Module R
 M] : Function.Surjective fun f : E ->ₗ[R] M => f ∘ₗ p.subtype
参数：h : IsComplemented p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surjective_comp_subtype_of_isComplemented (h : IsComplemented p) [Module R M] :
    Function.Surjective fun f : E →ₗ[R] M ↦ f ∘ₗ p.subtype :=
  have ⟨q, h⟩ := h; fun f ↦ ⟨f ∘ₗ p.projectionOnto q h, by ext; simp⟩

@[simp]
/-
**LinearMap.range_ofIsCompl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_ofIsCompl (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} : ra
nge (ofIsCompl hpq φ ψ) = range φ ⊔ range ψ
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ofIsCompl_eq_add`：ofIsCompl_eq_add (hpq : IsCompl p q) {φ : p 
->ₗ[R] F} {ψ : q ->ₗ[R] F} : ofIsCompl hpq φ ψ = (φ ∘ₗ p.projectionOnto q hpq) +
 (ψ ∘ₗ q.project…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LinearMap.range_add_le`：range_add_le [RingHomSurjective τ₁₂] (f g : M ->
ₛₗ[τ₁₂] M₂) : range (f + g) <= range f ⊔ range g
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `Submodule.projectionOnto_apply_right`：projectionOnto_apply_right (h : Is
Compl p q) (x : q) : projectionOnto p q h x = 0
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem range_ofIsCompl (hpq : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} :
    range (ofIsCompl hpq φ ψ) = range φ ⊔ range ψ := by
  rw [ofIsCompl_eq_add]
  apply le_antisymm
  · apply range_add_le _ _ |>.trans
    gcongr
    all_goals exact range_comp_le_range ..
  · apply sup_le
    all_goals rintro - ⟨x, rfl⟩; exact ⟨x, by simp⟩
/-
**LinearMap.ofIsCompl_subtype_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_subtype_zero_eq (hpq : IsCompl p q) : ofIsCompl hpq p.subtype 0 
= p.projection q hpq
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `LinearMap.ofIsCompl_eq_add`：ofIsCompl_eq_add (hpq : IsCompl p q) {φ : p 
->ₗ[R] F} {ψ : q ->ₗ[R] F} : ofIsCompl hpq φ ψ = (φ ∘ₗ p.projectionOnto q hpq) +
 (ψ ∘ₗ q.project…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsCompl_subtype_zero_eq (hpq : IsCompl p q) :
    ofIsCompl hpq p.subtype 0 = p.projection q hpq := by
  simp [ofIsCompl_eq_add, projection]
/-
**LinearMap.ofIsCompl_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsCompl_symm (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} : ofI
sCompl hpq.symm ψ φ = ofIsCompl hpq φ ψ
参数：hpq : IsCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ofIsCompl_eq_add`：ofIsCompl_eq_add (hpq : IsCompl p q) {φ : p 
->ₗ[R] F} {ψ : q ->ₗ[R] F} : ofIsCompl hpq φ ψ = (φ ∘ₗ p.projectionOnto q hpq) +
 (ψ ∘ₗ q.project…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsCompl_symm (hpq : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} :
    ofIsCompl hpq.symm ψ φ = ofIsCompl hpq φ ψ := by
  simp [ofIsCompl_eq_add, add_comm]

section

variable {R₁ : Type*} [CommRing R₁] [Module R₁ E] [Module R₁ F]

/-- The linear map from `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` to `E →ₗ[R₁] F`. -/
/-
**LinearMap.ofIsComplProd** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：ofIsComplProd {p q : Submodule R₁ E} (h : IsCompl p q) : (p ->ₗ[R₁] F) × (
q ->ₗ[R₁] F) ->ₗ[R₁] E ->ₗ[R₁] F where toFun φ
参数：h : IsCompl p q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` to `E →ₗ[R₁] F`.
-/
def ofIsComplProd {p q : Submodule R₁ E} (h : IsCompl p q) :
    (p →ₗ[R₁] F) × (q →ₗ[R₁] F) →ₗ[R₁] E →ₗ[R₁] F where
  toFun φ := ofIsCompl h φ.1 φ.2
  map_add' := by intro φ ψ; rw [Prod.snd_add, Prod.fst_add, ofIsCompl_add]
  map_smul' := by intro c φ; simp [Prod.smul_snd, Prod.smul_fst, ofIsCompl_smul]

@[simp]
/-
**LinearMap.ofIsComplProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ofIsComplProd_apply {p q : Submodule R₁ E} (h : IsCompl p q) (φ : (p ->ₗ[R
₁] F) × (q ->ₗ[R₁] F)) : ofIsComplProd h φ = ofIsCompl h φ.1 φ.2
参数：h : IsCompl p q；φ : (p ->ₗ[R₁] F) × (q ->ₗ[R₁] F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofIsComplProd_apply {p q : Submodule R₁ E} (h : IsCompl p q)
    (φ : (p →ₗ[R₁] F) × (q →ₗ[R₁] F)) : ofIsComplProd h φ = ofIsCompl h φ.1 φ.2 :=
  rfl

/-- The natural linear equivalence between `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` and `E →ₗ[R₁] F`. -/
/-
**LinearMap.ofIsComplProdEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：ofIsComplProdEquiv {p q : Submodule R₁ E} (h : IsCompl p q) : ((p ->ₗ[R₁] 
F) × (q ->ₗ[R₁] F)) ≃ₗ[R₁] E ->ₗ[R₁] F
参数：h : IsCompl p q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural linear equivalence between `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` and `E →ₗ[R
₁] F`.
-/
def ofIsComplProdEquiv {p q : Submodule R₁ E} (h : IsCompl p q) :
    ((p →ₗ[R₁] F) × (q →ₗ[R₁] F)) ≃ₗ[R₁] E →ₗ[R₁] F :=
  { ofIsComplProd h with
    invFun := fun φ => ⟨φ.domRestrict p, φ.domRestrict q⟩
    left_inv := fun φ ↦ by
      ext x
      · exact ofIsCompl_apply_left h x
      · exact ofIsCompl_apply_right h x
    right_inv := fun φ ↦ by
      ext x
      obtain ⟨a, b, hab, _⟩ := existsUnique_add_of_isCompl h x
      rw [← hab]; simp }

end

@[simp]
/-
**LinearMap.projectionOnto_of_proj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：projectionOnto_of_proj (f : E ->ₗ[R] p) (hf : forall x : p, f x = x) : p.p
rojectionOnto (ker f) (isCompl_of_proj hf) = f
参数：f : E ->ₗ[R] p；hf : forall x : p, f x = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.isCompl_of_proj`：isCompl_of_proj {f : E ->ₗ[R] p} (hf : forall
 x : p, f x = x) : IsCompl p (ker f)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup'`：mem_sup' : x in p ⊔ p' ↔ exists (y : p) (z : p'), (y
 : M) + z = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `Submodule.projectionOnto_apply_right`：projectionOnto_apply_right (h : Is
Compl p q) (x : q) : projectionOnto p q h x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LinearMap.map_coe_ker`：map_coe_ker (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f) : f 
x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projectionOnto_of_proj (f : E →ₗ[R] p) (hf : ∀ x : p, f x = x) :
    p.projectionOnto (ker f) (isCompl_of_proj hf) = f := by
  ext x
  have : x ∈ p ⊔ (ker f) := by simp only [(isCompl_of_proj hf).sup_eq_top, mem_top]
  rcases mem_sup'.1 this with ⟨x, y, rfl⟩
  simp [hf]

/-- If `f : E →ₗ[R] F` and `g : E →ₗ[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃ₗ[R] F × G`. -/
/-
**LinearMap.equivProdOfSurjectiveOfIsCompl** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`
。
形式化陈述：equivProdOfSurjectiveOfIsCompl (f : E ->ₗ[R] F) (g : E ->ₗ[R] G) (hf : ran
ge f = ⊤) (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : E ≃ₗ[R] F × G
参数：f : E ->ₗ[R] F；g : E ->ₗ[R] G；hf : range f = ⊤；hg : range g = ⊤；hfg : IsCompl
 (ker f) (ker g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : E →ₗ[R] F` and `g : E →ₗ[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃ₗ[R] F × G`.
-/
def equivProdOfSurjectiveOfIsCompl (f : E →ₗ[R] F) (g : E →ₗ[R] G) (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : E ≃ₗ[R] F × G :=
  LinearEquiv.ofBijective (f.prod g)
    ⟨by simp [← ker_eq_bot, hfg.inf_eq_bot], by
      rw [← range_eq_top]
      simp [range_prod_eq hfg.sup_eq_top, *]⟩

@[simp]
/-
**LinearMap.coe_equivProdOfSurjectiveOfIsCompl** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：coe_equivProdOfSurjectiveOfIsCompl {f : E ->ₗ[R] F} {g : E ->ₗ[R] G} (hf :
 range f = ⊤) (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : (equivProdOfS
urjectiveOfIsCompl f g hf hg hfg : E ->ₗ[R] F × G) = f.prod g
参数：hf : range f = ⊤；hg : range g = ⊤；hfg : IsCompl (ker f) (ker g)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivProdOfSurjectiveOfIsCompl {f : E →ₗ[R] F} {g : E →ₗ[R] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E →ₗ[R] F × G) = f.prod g := rfl

@[simp]
/-
**LinearMap.equivProdOfSurjectiveOfIsCompl_apply** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：equivProdOfSurjectiveOfIsCompl_apply {f : E ->ₗ[R] F} {g : E ->ₗ[R] G} (hf
 : range f = ⊤) (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) (x : E) : equ
ivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x)
参数：hf : range f = ⊤；hg : range g = ⊤；hfg : IsCompl (ker f) (ker g)；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivProdOfSurjectiveOfIsCompl_apply {f : E →ₗ[R] F} {g : E →ₗ[R] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) := rfl

end LinearMap

namespace Submodule

open LinearMap

/-- Equivalence between submodules `q` such that `IsCompl p q` and linear maps `f : E →ₗ[R] p`
such that `∀ x : p, f x = x`. -/
/-
**Submodule.isComplEquivProj** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：isComplEquivProj : { q // IsCompl p q } ≃ { f : E ->ₗ[R] p // forall x : p
, f x = x } where toFun q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between submodules `q` such that `IsCompl p q` and linear maps `f : 
E →ₗ[R] p`
such that `∀ x : p, f x = x`.
-/
def isComplEquivProj : { q // IsCompl p q } ≃ { f : E →ₗ[R] p // ∀ x : p, f x = x } where
  toFun q := ⟨projectionOnto p q q.2, projectionOnto_apply_left q.2⟩
  invFun f := ⟨ker (f : E →ₗ[R] p), isCompl_of_proj f.2⟩
  left_inv := fun ⟨q, hq⟩ => by simp only [ker_projectionOnto]
  right_inv := fun ⟨f, hf⟩ => Subtype.ext <| f.projectionOnto_of_proj hf

@[simp]
/-
**Submodule.coe_isComplEquivProj_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_isComplEquivProj_apply (q : { q // IsCompl p q }) : (p.isComplEquivPro
j q : E ->ₗ[R] p) = projectionOnto p q q.2
参数：q : { q // IsCompl p q }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_isComplEquivProj_apply (q : { q // IsCompl p q }) :
    (p.isComplEquivProj q : E →ₗ[R] p) = projectionOnto p q q.2 := rfl

@[simp]
/-
**Submodule.coe_isComplEquivProj_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：coe_isComplEquivProj_symm_apply (f : { f : E ->ₗ[R] p // forall x : p, f x
 = x }) : (p.isComplEquivProj.symm f : Submodule R E) = ker (f : E ->ₗ[R] p)
参数：f : { f : E ->ₗ[R] p // forall x : p, f x = x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_isComplEquivProj_symm_apply (f : { f : E →ₗ[R] p // ∀ x : p, f x = x }) :
    (p.isComplEquivProj.symm f : Submodule R E) = ker (f : E →ₗ[R] p) := rfl

/-- The idempotent endomorphisms of a module with range equal to a submodule are in 1-1
correspondence with linear maps to the submodule that restrict to the identity on the submodule. -/
/-
**Submodule.isIdempotentElemEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   [inst : Ring R] →     {E : Type u_2} →       [inst_1 : 
AddCommGroup E] →         [inst_2 : _root_.Module R E] →           (p : Submodul
e R E) → { f // IsIdempotentElem f ∧ LinearMap.range f = p } ≃ { f // ∀ (x : ↥p)
, f ↑x = x }
参数：p : Submodule R E；x : ↥p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The idempotent endomorphisms of a module with range equal to a submodule are in 
1-1
correspondence with linear maps to the submodule that restrict to the identity o
n the submodule.
-/
@[simps] def isIdempotentElemEquiv :
    { f : Module.End R E // IsIdempotentElem f ∧ range f = p } ≃
    { f : E →ₗ[R] p // ∀ x : p, f x = x } where
  toFun f := ⟨f.1.codRestrict _ fun x ↦ by simp_rw [← f.2.2]; exact mem_range_self f.1 x,
    fun ⟨x, hx⟩ ↦ Subtype.ext <| by
      obtain ⟨x, rfl⟩ := f.2.2.symm ▸ hx
      exact DFunLike.congr_fun f.2.1 x⟩
  invFun f := ⟨p.subtype ∘ₗ f.1, LinearMap.ext fun x ↦ by simp [f.2], le_antisymm
    ((range_comp_le_range _ _).trans_eq p.range_subtype)
    fun x hx ↦ ⟨x, Subtype.ext_iff.1 <| f.2 ⟨x, hx⟩⟩⟩

end Submodule

namespace LinearMap

open Submodule

/--
A linear endomorphism of a module `E` is a projection onto a submodule `p` if it sends every element
of `E` to `p` and fixes every element of `p`.
The definition allow more generally any `FunLike` type and not just linear maps, so that it can be
used for example with `ContinuousLinearMap` or `Matrix`.
-/
/-
**LinearMap.IsProj** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：{S : Type u_5} →   [inst : Semiring S] →     {M : Type u_6} →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module S M] → Submodule S M → {F
 : Type u_7} → [FunLike F M M] → F → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear endomorphism of a module `E` is a projection onto a submodule `p` if it
 sends every element
of `E` to `p` and fixes every element of `p`.
The definition allow more generally any `FunLike` type and not just linear maps,
 so that it can be
used for example with `ContinuousLinearMap` or `Matrix`.
-/
structure IsProj {F : Type*} [FunLike F M M] (f : F) : Prop where
  map_mem : ∀ x, f x ∈ m
  map_id : ∀ x ∈ m, f x = x
/-
**LinearMap.isProj_range_iff_isIdempotentElem** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：isProj_range_iff_isIdempotentElem (f : M ->ₗ[S] M) : IsProj (range f) f ↔ 
IsIdempotentElem f
参数：f : M ->ₗ[S] M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
-/
theorem isProj_range_iff_isIdempotentElem (f : M →ₗ[S] M) :
    IsProj (range f) f ↔ IsIdempotentElem f := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hf =>
    ⟨fun x => mem_range_self f x, fun x ⟨y, hy⟩ => by rw [← hy, ← Module.End.mul_apply, hf.eq]⟩⟩
  ext x
  exact h2 (f x) (h1 x)

alias ⟨_, IsIdempotentElem.isProj_range⟩ := isProj_range_iff_isIdempotentElem
/-
**LinearMap.isProj_iff_isIdempotentElem** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isProj_iff_isIdempotentElem (f : M ->ₗ[S] M) : (exists p : Submodule S M, 
IsProj p f) ↔ IsIdempotentElem f
参数：f : M ->ₗ[S] M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsProj.map_id`：∀ {S : Type u_5} [inst : Semiring S] {M : Type 
u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S 
M} {F : Type …
· 使用定理 `LinearMap.IsProj.map_mem`：∀ {S : Type u_5} [inst : Semiring S] {M : Type
 u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S
 M} {F : Type …
· 使用定理 `LinearMap.IsIdempotentElem.isProj_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   (
f : M →ₗ[S] M), IsIdempotentE…
-/
theorem isProj_iff_isIdempotentElem (f : M →ₗ[S] M) :
    (∃ p : Submodule S M, IsProj p f) ↔ IsIdempotentElem f := by
  refine ⟨fun ⟨p, hp⟩ => ?_, fun h => ⟨_, IsIdempotentElem.isProj_range _ h⟩⟩
  ext x
  exact hp.map_id (f x) (hp.map_mem x)

namespace IsProj

variable {p m}

/-
**LinearMap.IsProj.isIdempotentElem** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`
。
形式化陈述：isIdempotentElem {f : M ->ₗ[S] M} (h : IsProj m f) : IsIdempotentElem f
参数：h : IsProj m f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.isProj_iff_isIdempotentElem`：isProj_iff_isIdempotentElem (f : 
M ->ₗ[S] M) : (exists p : Submodule S M, IsProj p f) ↔ IsIdempotentElem f
-/
theorem isIdempotentElem {f : M →ₗ[S] M} (h : IsProj m f) : IsIdempotentElem f :=
  f.isProj_iff_isIdempotentElem.mp ⟨m, h⟩
/-
**LinearMap.IsProj.mem_iff_map_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`。
形式化陈述：mem_iff_map_id {f : M ->ₗ[S] M} (hf : IsProj m f) {x : M} : x in m ↔ f x =
 x
参数：hf : IsProj m f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.map_id`：∀ {S : Type u_5} [inst : Semiring S] {M : Type 
u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S 
M} {F : Type …
· 使用定理 `LinearMap.IsProj.map_mem`：∀ {S : Type u_5} [inst : Semiring S] {M : Type
 u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S
 M} {F : Type …
-/
theorem mem_iff_map_id {f : M →ₗ[S] M} (hf : IsProj m f) {x : M} :
    x ∈ m ↔ f x = x :=
  ⟨hf.map_id x, fun h ↦ h ▸ hf.map_mem x⟩

/-- Restriction of the codomain of a projection of onto a subspace `p` to `p` instead of the whole
space.
-/
/-
**LinearMap.IsProj.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.IsProj`。
形式化陈述：codRestrict {f : M ->ₗ[S] M} (h : IsProj m f) : M ->ₗ[S] m
参数：h : IsProj m f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of the codomain of a projection of onto a subspace `p` to `p` instea
d of the whole
space.
-/
def codRestrict {f : M →ₗ[S] M} (h : IsProj m f) : M →ₗ[S] m :=
  f.codRestrict m h.map_mem

@[simp]
/-
**LinearMap.IsProj.codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj
`。
形式化陈述：codRestrict_apply {f : M ->ₗ[S] M} (h : IsProj m f) (x : M) : ↑(h.codRestr
ict x) = f x
参数：h : IsProj m f；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.codRestrict_apply`：codRestrict_apply (p : Submodule R₂ M₂) (f 
: M ->ₛₗ[σ₁₂] M₂) {h} (x : M) : (codRestrict p f h x : M₂) = f x
-/
theorem codRestrict_apply {f : M →ₗ[S] M} (h : IsProj m f) (x : M) : ↑(h.codRestrict x) = f x :=
  f.codRestrict_apply m x

@[simp]
/-
**LinearMap.IsProj.codRestrict_apply_cod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Is
Proj`。
形式化陈述：codRestrict_apply_cod {f : M ->ₗ[S] M} (h : IsProj m f) (x : m) : h.codRes
trict x = x
参数：h : IsProj m f；x : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsProj.codRestrict_apply`：codRestrict_apply {f : M ->ₗ[S] M} (
h : IsProj m f) (x : M) : ↑(h.codRestrict x) = f x
· 使用定理 `LinearMap.IsProj.map_id`：∀ {S : Type u_5} [inst : Semiring S] {M : Type 
u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S 
M} {F : Type …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem codRestrict_apply_cod {f : M →ₗ[S] M} (h : IsProj m f) (x : m) : h.codRestrict x = x := by
  ext
  rw [codRestrict_apply]
  exact h.map_id x x.2
/-
**LinearMap.IsProj.codRestrict_ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`。
形式化陈述：codRestrict_ker {f : M ->ₗ[S] M} (h : IsProj m f) : ker h.codRestrict = ke
r f
参数：h : IsProj m f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
-/
theorem codRestrict_ker {f : M →ₗ[S] M} (h : IsProj m f) : ker h.codRestrict = ker f :=
  f.ker_codRestrict m _
/-
**LinearMap.IsProj.isCompl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`。
形式化陈述：isCompl {f : E ->ₗ[R] E} (h : IsProj p f) : IsCompl p (ker f)
参数：h : IsProj p f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsProj.codRestrict_ker`：codRestrict_ker {f : M ->ₗ[S] M} (h : 
IsProj m f) : ker h.codRestrict = ker f
· 使用定理 `LinearMap.isCompl_of_proj`：isCompl_of_proj {f : E ->ₗ[R] p} (hf : forall
 x : p, f x = x) : IsCompl p (ker f)
· 使用定理 `LinearMap.IsProj.codRestrict_apply_cod`：codRestrict_apply_cod {f : M ->ₗ
[S] M} (h : IsProj m f) (x : m) : h.codRestrict x = x
-/
theorem isCompl {f : E →ₗ[R] E} (h : IsProj p f) : IsCompl p (ker f) := by
  rw [← codRestrict_ker h]
  exact isCompl_of_proj h.codRestrict_apply_cod
/-
**LinearMap.IsProj.eq_conj_prod_map'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj
`。
形式化陈述：eq_conj_prod_map' {f : E ->ₗ[R] E} (h : IsProj p f) : f = (p.prodEquivOfIs
Compl (ker f) h.isCompl).toLinearMap ∘ₗ prodMap id 0 ∘ₗ (p.prodEquivOfIsCompl (k
er f) h.isCompl).symm.toLinearMap
参数：h : IsProj p f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.isCompl`：isCompl {f : E ->ₗ[R] E} (h : IsProj p f) : Is
Compl p (ker f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.eq_comp_toLinearMap_symm`：eq_comp_toLinearMap_symm (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁
₂.toLinearMap = g
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LinearMap.IsProj.map_id`：∀ {S : Type u_5} [inst : Semiring S] {M : Type 
u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S 
M} {F : Type …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearMap.map_coe_ker`：map_coe_ker (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f) : f 
x = 0
-/
theorem eq_conj_prod_map' {f : E →ₗ[R] E} (h : IsProj p f) :
    f = (p.prodEquivOfIsCompl (ker f) h.isCompl).toLinearMap ∘ₗ
        prodMap id 0 ∘ₗ (p.prodEquivOfIsCompl (ker f) h.isCompl).symm.toLinearMap := by
  rw [← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
  ext x
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inl, coprod_apply, coe_subtype,
      map_zero, add_zero, h.map_id x x.2, prodMap_apply, id_apply]
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inr, coprod_apply, map_zero,
      coe_subtype, zero_add, map_coe_ker, prodMap_apply, zero_apply, add_zero]
/-
**LinearMap.IsProj.submodule_unique** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`
。
形式化陈述：submodule_unique {f : M ->ₗ[S] M} {m₁ m₂ : Submodule S M} (hf₁ : IsProj m₁
 f) (hf₂ : IsProj m₂ f) : m₁ = m₂
参数：hf₁ : IsProj m₁ f；hf₂ : IsProj m₂ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsProj.mem_iff_map_id`：mem_iff_map_id {f : M ->ₗ[S] M} (hf : I
sProj m f) {x : M} : x in m ↔ f x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem submodule_unique {f : M →ₗ[S] M} {m₁ m₂ : Submodule S M}
    (hf₁ : IsProj m₁ f) (hf₂ : IsProj m₂ f) : m₁ = m₂ := by
  ext; simp [hf₁.mem_iff_map_id, hf₂.mem_iff_map_id]

open LinearMap in
/-
**LinearMap.IsProj.range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`。
形式化陈述：∀ {S : Type u_5} [inst : Semiring S] {M : Type u_6} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module S M]   {m : Submodule S M} {f : M →ₗ[S] M}, LinearM
ap.IsProj m f → f.range = m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.submodule_unique`：submodule_unique {f : M ->ₗ[S] M} {m₁
 m₂ : Submodule S M} (hf₁ : IsProj m₁ f) (hf₂ : IsProj m₂ f) : m₁ = m₂
· 使用定理 `LinearMap.IsIdempotentElem.isProj_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   (
f : M →ₗ[S] M), IsIdempotentE…
· 使用定理 `LinearMap.IsProj.isIdempotentElem`：isIdempotentElem {f : M ->ₗ[S] M} (h 
: IsProj m f) : IsIdempotentElem f
-/
protected theorem range {f : M →ₗ[S] M} (h : IsProj m f) : range f = m :=
  h.isIdempotentElem.isProj_range.submodule_unique h

variable (S M) in
/-
**LinearMap.IsProj.bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`。
形式化陈述：∀ (S : Type u_5) [inst : Semiring S] (M : Type u_6) [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module S M],   LinearMap.IsProj ⊥ 0
参数：S : Type u_5；M : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem bot : IsProj (⊥ : Submodule S M) (0 : M →ₗ[S] M) :=
  ⟨congrFun rfl, by simp only [mem_bot, zero_apply, forall_eq]⟩

variable (S M) in
/-
**LinearMap.IsProj.top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`。
形式化陈述：∀ (S : Type u_5) [inst : Semiring S] (M : Type u_6) [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module S M],   LinearMap.IsProj ⊤ LinearMap.id
参数：S : Type u_5；M : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
protected theorem top : IsProj (⊤ : Submodule S M) (id (R := S)) :=
  ⟨fun _ ↦ trivial, fun _ ↦ congrFun rfl⟩
/-
**LinearMap.IsProj.subtype_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.IsProj`。
形式化陈述：subtype_comp_codRestrict {U : Submodule S M} {f : M ->ₗ[S] M} (hf : IsProj
 U f) : U.subtype ∘ₗ hf.codRestrict = f
参数：hf : IsProj U f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_comp_codRestrict {U : Submodule S M} {f : M →ₗ[S] M} (hf : IsProj U f) :
    U.subtype ∘ₗ hf.codRestrict = f := rfl
/-
**LinearMap.IsProj.submodule_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsP
roj`。
形式化陈述：submodule_eq_top_iff {f : M ->ₗ[S] M} (hf : IsProj m f) : m = (⊤ : Submodu
le S M) ↔ f = LinearMap.id
参数：hf : IsProj m f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsProj.map_id`：∀ {S : Type u_5} [inst : Semiring S] {M : Type 
u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S 
M} {F : Type …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsProj.range`：∀ {S : Type u_5} [inst : Semiring S] {M : Type u
_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S M
} {f : M →ₗ[…
· 使用定理 `LinearMap.range_id`：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
-/
theorem submodule_eq_top_iff {f : M →ₗ[S] M} (hf : IsProj m f) :
    m = (⊤ : Submodule S M) ↔ f = LinearMap.id := by
  constructor <;> rintro rfl
  · ext
    simp [hf.map_id]
  · rw [← hf.range, range_id]
/-
**LinearMap.IsProj.submodule_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsP
roj`。
形式化陈述：submodule_eq_bot_iff {f : M ->ₗ[S] M} (hf : IsProj m f) : m = (⊥ : Submodu
le S M) ↔ f = 0
参数：hf : IsProj m f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsProj.map_mem`：∀ {S : Type u_5} [inst : Semiring S] {M : Type
 u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S
 M} {F : Type …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsProj.range`：∀ {S : Type u_5} [inst : Semiring S] {M : Type u
_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S M
} {f : M →ₗ[…
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
-/
theorem submodule_eq_bot_iff {f : M →ₗ[S] M} (hf : IsProj m f) :
    m = (⊥ : Submodule S M) ↔ f = 0 := by
  constructor <;> rintro rfl
  · ext
    simpa using hf.map_mem _
  · rw [← hf.range, range_zero]

end IsProj

open LinearMap in
/-
**LinearMap.IsIdempotentElem.isCompl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsIdem
potentElem`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {E : Type u_2} [inst_1 : AddCommGroup E] 
[inst_2 : _root_.Module R E] {f : E →ₗ[R] E},   IsIdempotentElem f → IsCompl f.r
ange f.ker
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.isCompl`：isCompl {f : E ->ₗ[R] E} (h : IsProj p f) : Is
Compl p (ker f)
· 使用定理 `LinearMap.IsIdempotentElem.isProj_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   (
f : M →ₗ[S] M), IsIdempotentE…
-/
lemma IsIdempotentElem.isCompl {f : E →ₗ[R] E} (hf : IsIdempotentElem f) :
    IsCompl (range f) (ker f) := hf.isProj_range.isCompl

open LinearMap in
/-- Given an idempotent linear operator `p`, we have
`x ∈ range p` if and only if `p(x) = x` for all `x`. -/
/-
**LinearMap.IsIdempotentElem.mem_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.
IsIdempotentElem`。
形式化陈述：∀ {S : Type u_5} [inst : Semiring S] {M : Type u_6} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module S M]   {p : M →ₗ[S] M}, IsIdempotentElem p → ∀ {x :
 M}, x ∈ p.range ↔ p x = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.mem_iff_map_id`：mem_iff_map_id {f : M ->ₗ[S] M} (hf : I
sProj m f) {x : M} : x in m ↔ f x = x
· 使用定理 `LinearMap.IsIdempotentElem.isProj_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   (
f : M →ₗ[S] M), IsIdempotentE…

--- 原说明 ---
Given an idempotent linear operator `p`, we have
`x ∈ range p` if and only if `p(x) = x` for all `x`.
-/
theorem IsIdempotentElem.mem_range_iff {p : M →ₗ[S] M} (hp : IsIdempotentElem p) {x : M} :
    x ∈ range p ↔ p x = x := hp.isProj_range.mem_iff_map_id

open LinearMap in
/-- An idempotent linear operator is equal to the linear projection onto
its range along its kernel. -/
/-
**LinearMap.IsIdempotentElem.eq_projection** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.
IsIdempotentElem`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {E : Type u_2} [inst_1 : AddCommGroup E] 
[inst_2 : _root_.Module R E] {T : E →ₗ[R] E}   (hT : IsIdempotentElem T), T = T.
range.projection T.ker ⋯
参数：hT : IsIdempotentElem T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsIdempotentElem.isCompl`：∀ {R : Type u_1} [inst : Ring R] {E 
: Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E] {f : E →ₗ[R] 
E},   IsIdempotentElem f…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ofIsCompl_eq`：ofIsCompl_eq (h : IsCompl p q) {φ : p ->ₗ[R] F} 
{ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F} (hφ : forall u, φ u = χ u) (hψ : forall u, ψ u
 = χ u) : of…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsProj.map_id`：∀ {S : Type u_5} [inst : Semiring S] {M : Type 
u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   {m : Submodule S 
M} {F : Type …
· 使用定理 `LinearMap.IsIdempotentElem.isProj_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   (
f : M →ₗ[S] M), IsIdempotentE…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearMap.map_coe_ker`：map_coe_ker (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f) : f 
x = 0
· 使用定理 `LinearMap.ofIsCompl_subtype_zero_eq`：ofIsCompl_subtype_zero_eq (hpq : Is
Compl p q) : ofIsCompl hpq p.subtype 0 = p.projection q hpq

--- 原说明 ---
An idempotent linear operator is equal to the linear projection onto
its range along its kernel.
-/
theorem IsIdempotentElem.eq_projection {T : E →ₗ[R] E} (hT : IsIdempotentElem T) :
    T = T.range.projection T.ker hT.isCompl := by
  convert! ofIsCompl_subtype_zero_eq hT.isCompl
  exact ofIsCompl_eq _ (by simp [hT.isProj_range.map_id]) (by simp) |>.symm

open LinearMap in
/-- A linear map is an idempotent if and only if it equals the projection
onto its range along its kernel. -/
/-
**LinearMap.isIdempotentElem_iff_eq_projection_range_ker** 是 Mathlib 中的一个定理，位于命名
空间 `LinearMap`。
形式化陈述：isIdempotentElem_iff_eq_projection_range_ker {T : E ->ₗ[R] E} : IsIdempote
ntElem T ↔ exists (h : IsCompl (range T) (ker T)), T = T.range.projection T.ker 
h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.isCompl`：isCompl {f : E ->ₗ[R] E} (h : IsProj p f) : Is
Compl p (ker f)
· 使用定理 `LinearMap.IsIdempotentElem.isProj_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   (
f : M →ₗ[S] M), IsIdempotentE…
· 使用定理 `LinearMap.IsIdempotentElem.eq_projection`：∀ {R : Type u_1} [inst : Ring 
R] {E : Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E] {T : E 
→ₗ[R] E}   (hT : IsIdempotentE…
· 使用定理 `Submodule.isIdempotentElem_projection`：isIdempotentElem_projection (hpq 
: IsCompl p q) : IsIdempotentElem (p.projection q hpq)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A linear map is an idempotent if and only if it equals the projection
onto its range along its kernel.
-/
theorem isIdempotentElem_iff_eq_projection_range_ker {T : E →ₗ[R] E} :
    IsIdempotentElem T ↔ ∃ (h : IsCompl (range T) (ker T)), T = T.range.projection T.ker h :=
  ⟨fun hT => ⟨hT.isProj_range.isCompl, hT.eq_projection⟩,
   fun ⟨hT, h⟩ => h.symm ▸ isIdempotentElem_projection hT⟩

open LinearMap in
/-- Given an idempotent linear operator `q`,
we have `q ∘ p = p` iff `range p ⊆ range q` for all `p`. -/
/-
**LinearMap.IsIdempotentElem.comp_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.IsIdempotentElem`。
形式化陈述：∀ {S : Type u_5} [inst : Semiring S] {M : Type u_6} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module S M]   {q : M →ₗ[S] M},   IsIdempotentElem q →     
∀ {E : Type u_7} [inst_3 : AddCommMonoid E] [inst_4 : _root_.Module S E] (p : E 
→ₗ[S] M),       q ∘ₗ p = p ↔ p.range ≤ q.range
参数：p : E →ₗ[S] M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsIdempotentElem.mem_range_iff`：∀ {S : Type u_5} [inst : Semir
ing S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   
{p : M →ₗ[S] M}, IsIdempotentE…
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given an idempotent linear operator `q`,
we have `q ∘ p = p` iff `range p ⊆ range q` for all `p`.
-/
theorem IsIdempotentElem.comp_eq_right_iff {q : M →ₗ[S] M} (hq : IsIdempotentElem q)
    {E : Type*} [AddCommMonoid E] [Module S E] (p : E →ₗ[S] M) :
    q.comp p = p ↔ range p ≤ range q := by
  simp_rw [LinearMap.ext_iff, comp_apply, ← hq.mem_range_iff,
    SetLike.le_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]

open LinearMap in
/-- Idempotent operators are equal iff their range and kernels are. -/
/-
**LinearMap.IsIdempotentElem.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsIdem
potentElem`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {E : Type u_2} [inst_1 : AddCommGroup E] 
[inst_2 : _root_.Module R E]   {p q : E →ₗ[R] E}, IsIdempotentElem p → IsIdempot
entElem q → (p = q ↔ p.range = q.range ∧ p.ker = q.ker)
参数：p = q ↔ p.range = q.range ∧ p.ker = q.ker。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.existsUnique_add_of_isCompl`：existsUnique_add_of_isCompl (hc :
 IsCompl p q) (x : E) : exists (u : p) (v : q), (u : E) + v = x ∧ forall (r : p)
 (s : q), (r : E) + s = x -…
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `LinearMap.IsIdempotentElem.isCompl`：∀ {R : Type u_1} [inst : Ring R] {E 
: Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E] {f : E →ₗ[R] 
E},   IsIdempotentElem f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `LinearMap.IsIdempotentElem.mem_range_iff`：∀ {S : Type u_5} [inst : Semir
ing S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   
{p : M →ₗ[S] M}, IsIdempotentE…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Idempotent operators are equal iff their range and kernels are.
-/
lemma IsIdempotentElem.ext_iff {p q : E →ₗ[R] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p = q ↔ range p = range q ∧ ker p = ker q := by
  refine ⟨fun h => ⟨congrArg range h, congrArg ker h⟩, fun ⟨hr, hk⟩ => ?_⟩
  ext x
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩, rfl, _⟩ :=
    (ker p).existsUnique_add_of_isCompl hp.isCompl.symm x
  simp [mem_ker.mp, hv, (hk ▸ hv), (mem_range_iff hp).mp, hw, (mem_range_iff hq).mp, (hr ▸ hw)]

alias ⟨_, IsIdempotentElem.ext⟩ := IsIdempotentElem.ext_iff
/-
**LinearMap.IsIdempotentElem.range_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.I
sIdempotentElem`。
形式化陈述：∀ {S : Type u_5} [inst : Semiring S] {E : Type u_7} [inst_1 : AddCommGroup
 E] [inst_2 : _root_.Module S E]   {p : E →ₗ[S] E}, IsIdempotentElem p → p.range
 = (LinearMap.id - p).ker
参数：LinearMap.id - p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_le_ker_iff`：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M
₂ ->ₛₗ[τ₂₃] M₃} : range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0
· 使用引理 `IsIdempotentElem.one_sub_mul_self`：one_sub_mul_self (h : IsIdempotentEle
m a) : (1 - a) * a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem IsIdempotentElem.range_eq_ker {E : Type*} [AddCommGroup E] [Module S E]
    {p : E →ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.range p = LinearMap.ker (id - p) :=
  le_antisymm
    (LinearMap.range_le_ker_iff.mpr hp.one_sub_mul_self)
    fun x hx ↦ ⟨x, by simpa [sub_eq_zero, eq_comm (a := x)] using hx⟩
/-
**LinearMap.IsIdempotentElem.range_eq_ker_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.IsIdempotentElem`。
形式化陈述：∀ {S : Type u_5} [inst : Semiring S] {E : Type u_7} [inst_1 : AddCommGroup
 E] [inst_2 : _root_.Module S E]   {p : E →ₗ[S] E}, IsIdempotentElem p → p.range
 = (1 - p).ker
参数：1 - p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsIdempotentElem.range_eq_ker`：∀ {S : Type u_5} [inst : Semiri
ng S] {E : Type u_7} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module S E]   {p
 : E →ₗ[S] E}, IsIdempotentEl…
-/
theorem IsIdempotentElem.range_eq_ker_one_sub {E : Type*} [AddCommGroup E] [Module S E]
    {p : E →ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.range p = LinearMap.ker (1 - p) :=
  range_eq_ker hp

open LinearMap in
/-
**LinearMap.IsIdempotentElem.ker_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.I
sIdempotentElem`。
形式化陈述：∀ {S : Type u_5} [inst : Semiring S] {E : Type u_7} [inst_1 : AddCommGroup
 E] [inst_2 : _root_.Module S E]   {p : E →ₗ[S] E}, IsIdempotentElem p → p.ker =
 (LinearMap.id - p).range
参数：LinearMap.id - p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsIdempotentElem.range_eq_ker_one_sub`：∀ {S : Type u_5} [inst 
: Semiring S] {E : Type u_7} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module S
 E]   {p : E →ₗ[S] E}, IsIdempotentEl…
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
-/
theorem IsIdempotentElem.ker_eq_range {E : Type*} [AddCommGroup E] [Module S E]
    {p : E →ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.ker p = LinearMap.range (id - p) := by
  simpa using! hp.one_sub.range_eq_ker_one_sub.symm
/-
**LinearMap.IsIdempotentElem.ker_eq_range_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.IsIdempotentElem`。
形式化陈述：∀ {S : Type u_5} [inst : Semiring S] {E : Type u_7} [inst_1 : AddCommGroup
 E] [inst_2 : _root_.Module S E]   {p : E →ₗ[S] E}, IsIdempotentElem p → p.ker =
 (1 - p).range
参数：1 - p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsIdempotentElem.ker_eq_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {E : Type u_7} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module S E]   {p
 : E →ₗ[S] E}, IsIdempotentEl…
-/
theorem IsIdempotentElem.ker_eq_range_one_sub {E : Type*} [AddCommGroup E] [Module S E]
    {p : E →ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.ker p = LinearMap.range (1 - p) :=
  ker_eq_range hp

open LinearMap in
/-
**LinearMap.IsIdempotentElem.comp_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.IsIdempotentElem`。
形式化陈述：∀ {S : Type u_5} [inst : Semiring S] {M : Type u_7} [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module S M]   {q : M →ₗ[S] M},   IsIdempotentElem q →     ∀
 {E : Type u_8} [inst_3 : AddCommGroup E] [inst_4 : _root_.Module S E] (p : M →ₗ
[S] E), p ∘ₗ q = p ↔ q.ker ≤ p.ker
参数：p : M →ₗ[S] E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.IsIdempotentElem.ker_eq_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {E : Type u_7} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module S E]   {p
 : E →ₗ[S] E}, IsIdempotentEl…
· 使用定理 `LinearMap.comp_sub`：comp_sub (f g : M ->ₛₗ[σ₁₂] N₂) (h : N₂ ->ₛₗ[σ₂₃] N₃
) : h.comp (g - f) = h.comp g - h.comp f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsIdempotentElem.comp_eq_left_iff {M : Type*} [AddCommGroup M] [Module S M] {q : M →ₗ[S] M}
    (hq : IsIdempotentElem q) {E : Type*} [AddCommGroup E] [Module S E] (p : M →ₗ[S] E) :
    p ∘ₗ q = p ↔ ker q ≤ ker p := by
  simp [hq.ker_eq_range, range_le_ker_iff, comp_sub, sub_eq_zero, eq_comm]

end LinearMap

end Ring

section CommRing

namespace LinearMap

variable {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E] {p : Submodule R E}

/-
**LinearMap.IsProj.eq_conj_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {E : Type u_2} [inst_1 : AddCommGroup
 E] [inst_2 : _root_.Module R E]   {p : Submodule R E} {f : E →ₗ[R] E} (h : Line
arMap.IsProj p f),   f = (p.prodEquivOfIsCompl f.ker ⋯).conj (LinearMap.id.prodM
ap 0)
参数：h : LinearMap.IsProj p f；p.prodEquivOfIsCompl f.ker ⋯；LinearMap.id.prodMap 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.isCompl`：isCompl {f : E ->ₗ[R] E} (h : IsProj p f) : Is
Compl p (ker f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.conj_apply`：conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.
End R₁' M₁') : e.conj f = ((↑e : M₁' ->ₛₗ[σ₁'₂'] M₂').comp f).comp (e.symm : M₂'
 ->ₛₗ[σ₂'₁']…
· 使用定理 `LinearMap.IsProj.eq_conj_prod_map'`：eq_conj_prod_map' {f : E ->ₗ[R] E} (
h : IsProj p f) : f = (p.prodEquivOfIsCompl (ker f) h.isCompl).toLinearMap ∘ₗ pr
odMap id 0 ∘ₗ (p.prodEqu…
-/
theorem IsProj.eq_conj_prodMap {f : E →ₗ[R] E} (h : IsProj p f) :
    f = (p.prodEquivOfIsCompl (ker f) h.isCompl).conj (prodMap id 0) := by
  rw [LinearEquiv.conj_apply]
  exact h.eq_conj_prod_map'

end LinearMap

end CommRing

namespace LinearMap.IsIdempotentElem

open Submodule LinearMap

variable {E R : Type*} [Ring R] [AddCommGroup E] [Module R E] {T f : E →ₗ[R] E}

/-- `range f` is invariant under `T` if and only if `f ∘ₗ T ∘ₗ f = T ∘ₗ f`,
for idempotent `f`. -/
/-
**LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff** 是 Mathlib 中的一个引理，位于命名
空间 `LinearMap.IsIdempotentElem`。
形式化陈述：range_mem_invtSubmodule_iff (hf : IsIdempotentElem f) : range f in Module.
End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = T ∘ₗ f
参数：hf : IsIdempotentElem f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsIdempotentElem.comp_eq_right_iff`：∀ {S : Type u_5} [inst : S
emiring S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M
]   {q : M →ₗ[S] M},   IsIdempoten…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Module.End.mem_invtSubmodule_iff_map_le`：mem_invtSubmodule_iff_map_le {p
 : Submodule R M} : p in f.invtSubmodule ↔ p.map f <= p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`range f` is invariant under `T` if and only if `f ∘ₗ T ∘ₗ f = T ∘ₗ f`,
for idempotent `f`.
-/
lemma range_mem_invtSubmodule_iff (hf : IsIdempotentElem f) :
    range f ∈ Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = T ∘ₗ f := by
  rw [hf.comp_eq_right_iff, range_comp, Module.End.mem_invtSubmodule_iff_map_le]

alias ⟨conj_eq_of_range_mem_invtSubmodule, range_mem_invtSubmodule⟩ := range_mem_invtSubmodule_iff
/-
**LinearMap.IsIdempotentElem._root_.LinearMap.IsProj.mem_invtSubmodule_iff** 是 M
athlib 中的一个引理，位于命名空间 `LinearMap.IsIdempotentElem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.IsProj.mem_invtSubmodule_iff {U : Submodule R E}
    (hf : IsProj U f) : U ∈ Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = T ∘ₗ f :=
  hf.range ▸ hf.isIdempotentElem.range_mem_invtSubmodule_iff

open LinearMap in
/-- `ker f` is invariant under `T` if and only if `f ∘ₗ T ∘ₗ f = f ∘ₗ T`,
for idempotent `f`. -/
/-
**LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间
 `LinearMap.IsIdempotentElem`。
形式化陈述：ker_mem_invtSubmodule_iff (hf : IsIdempotentElem f) : ker f in Module.End.
invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = f ∘ₗ T
参数：hf : IsIdempotentElem f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.IsIdempotentElem.comp_eq_left_iff`：∀ {S : Type u_5} [inst : Se
miring S] {M : Type u_7} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module S M] 
  {q : M →ₗ[S] M},   IsIdempotent…
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用引理 `Module.End.mem_invtSubmodule`：mem_invtSubmodule {p : Submodule R M} : p 
in f.invtSubmodule ↔ p <= p.comap f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`ker f` is invariant under `T` if and only if `f ∘ₗ T ∘ₗ f = f ∘ₗ T`,
for idempotent `f`.
-/
lemma ker_mem_invtSubmodule_iff (hf : IsIdempotentElem f) :
    ker f ∈ Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = f ∘ₗ T := by
  rw [← comp_assoc, hf.comp_eq_left_iff, ker_comp, Module.End.mem_invtSubmodule]

alias ⟨conj_eq_of_ker_mem_invtSubmodule, ker_mem_invtSubmodule⟩ := ker_mem_invtSubmodule_iff

/-- An idempotent operator `f` commutes with a linear operator `T` if and only if
both `range f` and `ker f` are invariant under `T`. -/
/-
**LinearMap.IsIdempotentElem.commute_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Is
IdempotentElem`。
形式化陈述：commute_iff (hf : IsIdempotentElem f) : Commute f T ↔ (range f in Module.E
nd.invtSubmodule T ∧ ker f in Module.End.invtSubmodule T)
参数：hf : IsIdempotentElem f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff`：range_mem_invtSu
bmodule_iff (hf : IsIdempotentElem f) : range f in Module.End.invtSubmodule T ↔ 
f ∘ₗ T ∘ₗ f = T ∘ₗ f
· 使用引理 `LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff`：ker_mem_invtSubmod
ule_iff (hf : IsIdempotentElem f) : ker f in Module.End.invtSubmodule T ↔ f ∘ₗ T
 ∘ₗ f = f ∘ₗ T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
An idempotent operator `f` commutes with a linear operator `T` if and only if
both `range f` and `ker f` are invariant under `T`.
-/
lemma commute_iff (hf : IsIdempotentElem f) :
    Commute f T ↔ (range f ∈ Module.End.invtSubmodule T ∧ ker f ∈ Module.End.invtSubmodule T) := by
  simp_rw [hf.range_mem_invtSubmodule_iff, hf.ker_mem_invtSubmodule_iff, ← Module.End.mul_eq_comp]
  exact ⟨fun h => (by simp [← h.eq, ← mul_assoc, hf.eq]), fun ⟨h1, h2⟩ => h2.symm.trans h1⟩

/-- An idempotent operator `f` commutes with a unit operator `T` if and only if
`T (range f) = range f` and `T (ker f) = ker f`. -/
/-
**LinearMap.IsIdempotentElem.commute_iff_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.IsIdempotentElem`。
形式化陈述：commute_iff_of_isUnit (hT : IsUnit T) (hf : IsIdempotentElem f) : Commute 
f T ↔ (range f).map T = range f ∧ (ker f).map T = ker f
参数：hT : IsUnit T；hf : IsIdempotentElem f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.IsIdempotentElem.commute_iff`：commute_iff (hf : IsIdempotentEl
em f) : Commute f T ↔ (range f in Module.End.invtSubmodule T ∧ ker f in Module.E
nd.invtSubmodule T)
· 使用定理 `LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap`：generalLin
earEquiv_to_linearMap (f : GeneralLinearGroup R M) : (generalLinearEquiv R M f :
 M ->ₗ[R] M) = f
· 使用定理 `Commute.units_inv_right`：units_inv_right : Commute a u -> Commute a ↑u⁻¹

--- 原说明 ---
An idempotent operator `f` commutes with a unit operator `T` if and only if
`T (range f) = range f` and `T (ker f) = ker f`.
-/
theorem commute_iff_of_isUnit (hT : IsUnit T) (hf : IsIdempotentElem f) :
    Commute f T ↔ (range f).map T = range f ∧ (ker f).map T = ker f := by
  lift T to GeneralLinearGroup R E using hT
  simp_rw [← GeneralLinearGroup.generalLinearEquiv_to_linearMap, le_antisymm_iff,
    ← Module.End.mem_invtSubmodule_iff_map_le, ← Module.End.mem_invtSubmodule_symm_iff_le_map,
    and_and_and_comm (c := (ker f ∈ _)), ← hf.commute_iff,
    GeneralLinearGroup.generalLinearEquiv_to_linearMap, iff_self_and]
  exact Commute.units_inv_right

end LinearMap.IsIdempotentElem

/-! ## Deprecated -/

namespace Submodule

@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl := projectionOnto
@[deprecated (since := "2026-05-04")] alias IsCompl.projection := projection
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_apply := projection_apply
@[deprecated (since := "2026-05-04")] alias coe_linearProjOfIsCompl_apply :=
  coe_projectionOnto_apply
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_apply_mem := projection_apply_mem
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_apply_left :=
  projectionOnto_apply_left
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_apply_left := projection_apply_left
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_range := range_projectionOnto
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_range := range_projection
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_surjective :=
  projectionOnto_surjective
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_apply_eq_zero_iff :=
  projectionOnto_apply_eq_zero_iff
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_apply_eq_zero_iff :=
  projection_apply_eq_zero_iff
@[deprecated (since := "2026-05-05")] alias linearProjOfIsCompl_apply_of_mem_right :=
  projectionOnto_apply_of_mem_right
@[deprecated (since := "2026-04-27")] alias linearProjOfIsCompl_apply_right' :=
  projectionOnto_apply_of_mem_right
@[deprecated (since := "2026-05-05")] alias IsCompl.projection_apply_of_mem_right :=
  projection_apply_of_mem_right
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_apply_right :=
  projectionOnto_apply_right
@[deprecated (since := "2026-05-05")] alias IsCompl.projection_apply_right :=
  projection_apply_right
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_ker := ker_projectionOnto
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_ker := ker_projection
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_comp_subtype :=
  projectionOnto_comp_subtype
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_isCompl_projection :=
  projectionOnto_projection
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_isIdempotentElem :=
  isIdempotentElem_projection
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_add_projection_eq_self :=
  projection_add_projection_eq_self
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_add_projection_eq_id :=
  projection_add_projection_eq_id
@[deprecated (since := "2026-05-05")] alias IsCompl.projection_eq_self_sub_projection :=
  projection_eq_self_sub_projection
@[deprecated (since := "2026-05-05")] alias IsCompl.projection_eq_id_sub_projection :=
  projection_eq_id_sub_projection
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_eq_self_iff := projection_eq_self_iff

end Submodule

namespace LinearMap

@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_of_proj := projectionOnto_of_proj
@[deprecated (since := "2026-05-04")] alias IsIdempotentElem.eq_isCompl_projection :=
  IsIdempotentElem.eq_projection
@[deprecated (since := "2026-05-04")] alias surjective_comp_linearProjOfIsCompl :=
  surjective_comp_projectionOnto
@[deprecated (since := "2026-05-04")] alias isIdempotentElem_iff_eq_isCompl_projection_range_ker :=
  isIdempotentElem_iff_eq_projection_range_ker
@[deprecated (since := "2026-05-16")] alias ofIsCompl_left_apply := ofIsCompl_apply_left
@[deprecated (since := "2026-05-16")] alias ofIsCompl_right_apply := ofIsCompl_apply_right

end LinearMap

