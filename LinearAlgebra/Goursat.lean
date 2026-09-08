/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.GroupTheory.Goursat
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Goursat's lemma for submodules

Let `M, N` be modules over a ring `R`. If `L` is a submodule of `M × N` which projects fully onto
both factors, then there exist submodules `M' ≤ M` and `N' ≤ N` such that `M' × N' ≤ L` and the
image of `L` in `(M ⧸ M') × (N ⧸ N')` is the graph of an isomorphism `M ⧸ M' ≃ₗ[R] N ⧸ N'`.
Equivalently, `L` is equal to the preimage in `M × N` of the graph of this isomorphism
`M ⧸ M' ≃ₗ[R] N ⧸ N'`.

`M'` and `N'` can be explicitly constructed as `Submodule.goursatFst L` and `Submodule.goursatSnd L`
respectively.
-/

@[expose] public section

open Function Set LinearMap

namespace Submodule
variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {L : Submodule R (M × N)}
  (hL₁ : Surjective (Prod.fst ∘ L.subtype)) (hL₂ : Surjective (Prod.snd ∘ L.subtype))

variable (L) in
/-- For `L` a submodule of `M × N`, `L.goursatFst` is the kernel of the projection map `L → N`,
considered as a submodule of `M`.

This is the first submodule appearing in Goursat's lemma. See `Subgroup.goursat`. -/
/-
**Submodule.goursatFst** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：goursatFst : Submodule R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `L` a submodule of `M × N`, `L.goursatFst` is the kernel of the projection m
ap `L → N`,
considered as a submodule of `M`.

This is the first submodule appearing in Goursat's lemma. See `Subgroup.goursat`
.
-/
def goursatFst : Submodule R M :=
  (LinearMap.ker <| (LinearMap.snd R M N).comp L.subtype).map ((LinearMap.fst R M N).comp L.subtype)


variable (L) in
/-- For `L` a subgroup of `M × N`, `L.goursatSnd` is the kernel of the projection map `L → M`,
considered as a subgroup of `N`.

This is the second subgroup appearing in Goursat's lemma. See `Subgroup.goursat`. -/
/-
**Submodule.goursatSnd** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：goursatSnd : Submodule R N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `L` a subgroup of `M × N`, `L.goursatSnd` is the kernel of the projection ma
p `L → M`,
considered as a subgroup of `N`.

This is the second subgroup appearing in Goursat's lemma. See `Subgroup.goursat`
.
-/
def goursatSnd : Submodule R N :=
  (LinearMap.ker <| (LinearMap.fst R M N).comp L.subtype).map ((LinearMap.snd R M N).comp L.subtype)
/-
**Submodule.goursatFst_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：goursatFst_toAddSubgroup : (goursatFst L).toAddSubgroup = L.toAddSubgroup.
goursatFst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma goursatFst_toAddSubgroup :
    (goursatFst L).toAddSubgroup = L.toAddSubgroup.goursatFst := by
  ext x
  simp [goursatFst, AddSubgroup.mem_goursatFst]
/-
**Submodule.goursatSnd_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：goursatSnd_toAddSubgroup : (goursatSnd L).toAddSubgroup = L.toAddSubgroup.
goursatSnd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma goursatSnd_toAddSubgroup :
    (goursatSnd L).toAddSubgroup = L.toAddSubgroup.goursatSnd := by
  ext x
  simp [goursatSnd, AddSubgroup.mem_goursatSnd]

variable (L) in
/-
**Submodule.goursatFst_prod_goursatSnd_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：goursatFst_prod_goursatSnd_le : L.goursatFst.prod L.goursatSnd <= L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.goursatFst_prod_goursatSnd_le`：∀ {G : Type u_1} {H : Type u_
2} [inst : AddGroup G] [inst_1 : AddGroup H] (I : AddSubgroup (G × H)),   I.gour
satFst.prod I.goursatSnd ≤ I
-/
lemma goursatFst_prod_goursatSnd_le : L.goursatFst.prod L.goursatSnd ≤ L := by
  simpa only [← toAddSubgroup_le, goursatFst_toAddSubgroup, goursatSnd_toAddSubgroup]
    using! L.toAddSubgroup.goursatFst_prod_goursatSnd_le

set_option backward.isDefEq.respectTransparency false in
include hL₁ hL₂ in
/-- **Goursat's lemma** for a submodule of a product with surjective projections.

If `L` is a submodule of `M × N` which projects fully on both factors, then there exist submodules
`M' ≤ M` and `N' ≤ N` such that `M' × N' ≤ L` and the image of `L` in `(M ⧸ M') × (N ⧸ N')` is the
graph of an isomorphism of `R`-modules `(M ⧸ M') ≃ (N ⧸ N')`.

`M` and `N` can be explicitly constructed as `L.goursatFst` and `L.goursatSnd` respectively. -/
/-
**Submodule.goursat_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：goursat_surjective : exists e : (M ⧸ L.goursatFst) ≃ₗ[R] N ⧸ L.goursatSnd,
 LinearMap.range ((L.goursatFst.mkQ.prodMap L.goursatSnd.mkQ).comp L.subtype) = 
e.graph
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_goursatFst`：∀ {G : Type u_1} {H : Type u_2} [inst : A
ddGroup G] [inst_1 : AddGroup H] {I : AddSubgroup (G × H)},   Function.Surjectiv
e (Prod.fst ∘ ⇑I.su…
· 使用定理 `AddSubgroup.normal_goursatSnd`：∀ {G : Type u_1} {H : Type u_2} [inst : A
ddGroup G] [inst_1 : AddGroup H] {I : AddSubgroup (G × H)},   Function.Surjectiv
e (Prod.snd ∘ ⇑I.su…
· 使用定理 `AddSubgroup.goursat_surjective`：∀ {G : Type u_1} {H : Type u_2} [inst : 
AddGroup G] [inst_1 : AddGroup H] {I : AddSubgroup (G × H)}   (hI₁ : Function.Su
rjective (Prod.fst ∘…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.smul_mk`：∀ {E : Type u_8} {α : Type u_9} {β : Type u_10} [inst : SM
ul E α] [inst_1 : SMul E β] (c : E) (a : α) (b : β),   c • (a, b) = (c • a, c • 
b)
· 使用定理 `AddMonoidHom.mem_range`：∀ {G : Type u_1} [inst : AddGroup G] {N : Type u
_5} [inst_1 : AddGroup N] {f : G →+ N} {y : N},   y ∈ f.range ↔ ∃ x, f x = y
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.toAddSubgroup_injective`：∀ {R : Type u} {M : Type v} [inst : R
ing R] [inst_1 : AddCommGroup M] {module_M : _root_.Module R M},   Function.Inje
ctive Submodule.toAddSu…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `Submodule.mem_toAddSubgroup`：mem_toAddSubgroup : x in p.toAddSubgroup ↔ 
x in p
· 使用定理 `LinearMap.mem_graph_iff`：mem_graph_iff (x : M × M₂) : x in f.graph ↔ x.2
 = f x.1
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
**Goursat's lemma** for a submodule of a product with surjective projections.

If `L` is a submodule of `M × N` which projects fully on both factors, then ther
e exist submodules
`M' ≤ M` and `N' ≤ N` such that `M' × N' ≤ L` and the image of `L` in `(M ⧸ M') 
× (N ⧸ N')` is the
graph of an isomorphism of `R`-modules `(M ⧸ M') ≃ (N ⧸ N')`.

`M` and `N` can be explicitly constructed as `L.goursatFst` and `L.goursatSnd` r
espectively.
-/
lemma goursat_surjective : ∃ e : (M ⧸ L.goursatFst) ≃ₗ[R] N ⧸ L.goursatSnd,
    LinearMap.range ((L.goursatFst.mkQ.prodMap L.goursatSnd.mkQ).comp L.subtype) = e.graph := by
  -- apply add-group result
  obtain ⟨(e : M ⧸ L.goursatFst ≃+ N ⧸ L.goursatSnd), he⟩ :=
    L.toAddSubgroup.goursat_surjective hL₁ hL₂
  -- check R-linearity of the map
  have (r : R) (x : M ⧸ L.goursatFst) : e (r • x) = r • e x := by
    change (r • x, r • e x) ∈ e.toAddMonoidHom.graph
    rw [← he, ← Prod.smul_mk]
    have : (x, e x) ∈ e.toAddMonoidHom.graph := rfl
    rw [← he, AddMonoidHom.mem_range] at this
    rcases this with ⟨⟨l, hl⟩, hl'⟩
    use ⟨r • l, L.smul_mem r hl⟩
    rw [← hl']
    rfl
  -- define the map as an R-linear equiv
  use { e with map_smul' := this }
  rw [← toAddSubgroup_injective.eq_iff]
  convert! he using 1
  ext v
  rw [mem_toAddSubgroup, mem_graph_iff, Eq.comm]
  rfl

/-- **Goursat's lemma** for an arbitrary submodule of a product.

If `L` is a submodule of `M × N`, then there exist submodules `M'' ≤ M' ≤ M` and `N'' ≤ N' ≤ N` such
that `L ≤ M' × N'`, and `L` is (the image in `M × N` of) the preimage of the graph of an `R`-linear
isomorphism `M' ⧸ M'' ≃ N' ⧸ N''`. -/
/-
**Submodule.goursat** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：goursat : exists (M' : Submodule R M) (N' : Submodule R N) (M'' : Submodul
e R M') (N'' : Submodule R N') (e : (M' ⧸ M'') ≃ₗ[R] N' ⧸ N''), L = (e.graph.com
ap <| M''.mkQ.prodMap N''.mkQ).map (M'.subtype.prodMap N'.subtype)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_fst`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : Sem
iring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _roo
t_.Modu…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `LinearMap.submoduleMap_surjective`：submoduleMap_surjective [RingHomSurje
ctive σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Function.Surjective (f.sub
moduleMap p)
· 使用定理 `LinearMap.coe_snd`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : Sem
iring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _roo
t_.Modu…
· 使用引理 `Submodule.goursat_surjective`：goursat_surjective : exists e : (M ⧸ L.gou
rsatFst) ≃ₗ[R] N ⧸ L.goursatSnd, LinearMap.range ((L.goursatFst.mkQ.prodMap L.go
ursatSnd.mkQ).comp…
· 使用定理 `Submodule.comap_map_eq_self`：comap_map_eq_self {f : M ->ₛₗ[τ₁₂] M₂} {p :
 Submodule R M} (h : LinearMap.ker f <= p) : comap f (map f p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LinearMap.ker_prodMap`：ker_prodMap (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) 
: ker (LinearMap.prodMap f g) = Submodule.prod (ker f) (ker g)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用引理 `Submodule.goursatFst_prod_goursatSnd_le`：goursatFst_prod_goursatSnd_le :
 L.goursatFst.prod L.goursatSnd <= L
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.prod_apply`：∀ {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Ty
pe y} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M
₂] [inst_3…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)

--- 原说明 ---
**Goursat's lemma** for an arbitrary submodule of a product.

If `L` is a submodule of `M × N`, then there exist submodules `M'' ≤ M' ≤ M` and
 `N'' ≤ N' ≤ N` such
that `L ≤ M' × N'`, and `L` is (the image in `M × N` of) the preimage of the gra
ph of an `R`-linear
isomorphism `M' ⧸ M'' ≃ N' ⧸ N''`.
-/
lemma goursat : ∃ (M' : Submodule R M) (N' : Submodule R N) (M'' : Submodule R M')
    (N'' : Submodule R N') (e : (M' ⧸ M'') ≃ₗ[R] N' ⧸ N''),
    L = (e.graph.comap <| M''.mkQ.prodMap N''.mkQ).map (M'.subtype.prodMap N'.subtype) := by
  let M' := L.map (LinearMap.fst ..)
  let N' := L.map (LinearMap.snd ..)
  let P : L →ₗ[R] M' := (LinearMap.fst ..).submoduleMap L
  let Q : L →ₗ[R] N' := (LinearMap.snd ..).submoduleMap L
  let L' : Submodule R (M' × N') := LinearMap.range (P.prod Q)
  have hL₁' : Surjective (Prod.fst ∘ L'.subtype) := by
    simp only [← coe_fst (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, fst_prod, range_eq_top] using
      (LinearMap.fst ..).submoduleMap_surjective L
  have hL₂' : Surjective (Prod.snd ∘ L'.subtype) := by
    simp only [← coe_snd (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, snd_prod, range_eq_top] using
      (LinearMap.snd ..).submoduleMap_surjective L
  obtain ⟨e, he⟩ := goursat_surjective hL₁' hL₂'
  use M', N', L'.goursatFst, L'.goursatSnd, e
  rw [← he]
  simp only [LinearMap.range_comp, Submodule.range_subtype, L', M', N', P, Q]
  rw [comap_map_eq_self]
  · ext ⟨m, n⟩
    constructor
    · simp only [mem_map, LinearMap.mem_range, LinearMap.prod_apply, Function.prod_apply,
      Subtype.exists, Prod.exists, LinearMap.prodMap_apply, subtype_apply, Prod.mk.injEq,
      Subtype.ext_iff, submoduleMap_coe_apply, fst_apply, snd_apply]
      grind
    · simp only [mem_map, LinearMap.mem_range, LinearMap.prod_apply, Function.prod_apply,
      Subtype.exists, Prod.exists, LinearMap.prodMap_apply, subtype_apply, Prod.mk.injEq,
      snd_apply, fst_apply, Subtype.ext_iff, submoduleMap_coe_apply]
      grind
  · convert! goursatFst_prod_goursatSnd_le (range <| P.prod Q)
    simp only [ker_prodMap, ker_mkQ, Submodule.ext_iff]
    grind

end Submodule

