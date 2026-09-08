/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Graph
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Goursat's lemma for subgroups

This file proves Goursat's lemma for subgroups.

If `I` is a subgroup of `G × H` which projects fully on both factors, then there exist normal
subgroups `G' ≤ G` and `H' ≤ H` such that `G' × H' ≤ I` and the image of `I` in `G ⧸ G' × H ⧸ H'` is
the graph of an isomorphism `G ⧸ G' ≃ H ⧸ H'`.

`G'` and `H'` can be explicitly constructed as `Subgroup.goursatFst I` and `Subgroup.goursatSnd I`
respectively.
-/

@[expose] public section

open Function Set

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] {I : Subgroup (G × H)}
  (hI₁ : Surjective (Prod.fst ∘ I.subtype)) (hI₂ : Surjective (Prod.snd ∘ I.subtype))

variable (I) in
/-- For `I` a subgroup of `G × H`, `I.goursatFst` is the kernel of the projection map `I → H`,
considered as a subgroup of `G`.

This is the first subgroup appearing in Goursat's lemma. See `Subgroup.goursat`. -/
@[to_additive
/-- For `I` a subgroup of `G × H`, `I.goursatFst` is the kernel of the projection map `I → H`,
considered as a subgroup of `G`.

This is the first subgroup appearing in Goursat's lemma. See `AddSubgroup.goursat`. -/]
/-
**Subgroup.goursatFst** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：goursatFst : Subgroup G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def goursatFst : Subgroup G :=
  ((MonoidHom.snd G H).comp I.subtype).ker.map ((MonoidHom.fst G H).comp I.subtype)

variable (I) in
/-- For `I` a subgroup of `G × H`, `I.goursatSnd` is the kernel of the projection map `I → G`,
considered as a subgroup of `H`.

This is the second subgroup appearing in Goursat's lemma. See `Subgroup.goursat`. -/
@[to_additive
/-- For `I` a subgroup of `G × H`, `I.goursatSnd` is the kernel of the projection map `I → G`,
considered as a subgroup of `H`.

This is the second subgroup appearing in Goursat's lemma. See `AddSubgroup.goursat`. -/]
/-
**Subgroup.goursatSnd** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：goursatSnd : Subgroup H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def goursatSnd : Subgroup H :=
  ((MonoidHom.fst G H).comp I.subtype).ker.map ((MonoidHom.snd G H).comp I.subtype)

@[to_additive (attr := simp)]
/-
**Subgroup.mem_goursatFst** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_goursatFst {g : G} : g in I.goursatFst ↔ (g, 1) in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_goursatFst {g : G} : g ∈ I.goursatFst ↔ (g, 1) ∈ I := by simp [goursatFst]

@[to_additive (attr := simp)]
/-
**Subgroup.mem_goursatSnd** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_goursatSnd {h : H} : h in I.goursatSnd ↔ (1, h) in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
lemma mem_goursatSnd {h : H} : h ∈ I.goursatSnd ↔ (1, h) ∈ I := by simp [goursatSnd]

include hI₁ in
/-
**Subgroup.normal_goursatFst** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {I : S
ubgroup (G × H)},   Function.Surjective (Prod.fst ∘ ⇑I.subtype) → I.goursatFst.N
ormal
参数：G × H；Prod.fst ∘ ⇑I.subtype。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.map`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} [i
nst_1 : Group N] {H : Subgroup G},   H.Normal → ∀ (f : G →* N), Function.Surject
ive ⇑f → …
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
-/
@[to_additive] lemma normal_goursatFst : I.goursatFst.Normal := .map inferInstance _ hI₁

include hI₂ in
/-
**Subgroup.normal_goursatSnd** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {I : S
ubgroup (G × H)},   Function.Surjective (Prod.snd ∘ ⇑I.subtype) → I.goursatSnd.N
ormal
参数：G × H；Prod.snd ∘ ⇑I.subtype。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.map`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} [i
nst_1 : Group N] {H : Subgroup G},   H.Normal → ∀ (f : G →* N), Function.Surject
ive ⇑f → …
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
-/
@[to_additive] lemma normal_goursatSnd : I.goursatSnd.Normal := .map inferInstance _ hI₂

include hI₁ hI₂ in
@[to_additive]
/-
**Subgroup.mk_goursatFst_eq_iff_mk_goursatSnd_eq** 是 Mathlib 中的一个引理，位于命名空间 `Subg
roup`。
形式化陈述：mk_goursatFst_eq_iff_mk_goursatSnd_eq {x y : G × H} (hx : x in I) (hy : y 
in I) : (x.1 : G ⧸ I.goursatFst) = y.1 ↔ (x.2 : H ⧸ I.goursatSnd) = y.2
参数：hx : x in I；hy : y in I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_goursatFst`：∀ {G : Type u_1} {H : Type u_2} [inst : Grou
p G] [inst_1 : Group H] {I : Subgroup (G × H)},   Function.Surjective (Prod.fst 
∘ ⇑I.subtype) → …
· 使用定理 `Subgroup.normal_goursatSnd`：∀ {G : Type u_1} {H : Type u_2} [inst : Grou
p G] [inst_1 : Group H] {I : Subgroup (G × H)},   Function.Surjective (Prod.snd 
∘ ⇑I.subtype) → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `div_mem`：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
-/
lemma mk_goursatFst_eq_iff_mk_goursatSnd_eq {x y : G × H} (hx : x ∈ I) (hy : y ∈ I) :
    (x.1 : G ⧸ I.goursatFst) = y.1 ↔ (x.2 : H ⧸ I.goursatSnd) = y.2 := by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  rw [eq_comm]
  simp only [QuotientGroup.eq_iff_div_mem, mem_goursatFst, mem_goursatSnd]
  constructor <;> intro h
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hx) hy
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hy) hx

variable (I) in
@[to_additive AddSubgroup.goursatFst_prod_goursatSnd_le]
/-
**Subgroup.goursatFst_prod_goursatSnd_le** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：goursatFst_prod_goursatSnd_le : I.goursatFst.prod I.goursatSnd <= I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subgroup.mem_goursatFst`：mem_goursatFst {g : G} : g in I.goursatFst ↔ (g
, 1) in I
· 使用引理 `Subgroup.mem_goursatSnd`：mem_goursatSnd {h : H} : h in I.goursatSnd ↔ (1
, h) in I
-/
lemma goursatFst_prod_goursatSnd_le : I.goursatFst.prod I.goursatSnd ≤ I := by
  rintro ⟨g, h⟩ ⟨hg, hh⟩
  simpa using mul_mem (mem_goursatFst.1 hg) (mem_goursatSnd.1 hh)

/-- **Goursat's lemma** for a subgroup of a product with surjective projections.

If `I` is a subgroup of `G × H` which projects fully on both factors, then there exist normal
subgroups `M ≤ G` and `N ≤ H` such that `G' × H' ≤ I` and the image of `I` in `G ⧸ M × H ⧸ N` is the
graph of an isomorphism `G ⧸ M ≃ H ⧸ N'`.

`G'` and `H'` can be explicitly constructed as `I.goursatFst` and `I.goursatSnd` respectively. -/
@[to_additive
/-- **Goursat's lemma** for a subgroup of a product with surjective projections.

If `I` is a subgroup of `G × H` which projects fully on both factors, then there exist normal
subgroups `M ≤ G` and `N ≤ H` such that `G' × H' ≤ I` and the image of `I` in `G ⧸ M × H ⧸ N` is the
graph of an isomorphism `G ⧸ M ≃ H ⧸ N'`.

`G'` and `H'` can be explicitly constructed as `I.goursatFst` and `I.goursatSnd` respectively. -/]
/-
**Subgroup.goursat_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：goursat_surjective : have
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_goursatFst`：∀ {G : Type u_1} {H : Type u_2} [inst : Grou
p G] [inst_1 : Group H] {I : Subgroup (G × H)},   Function.Surjective (Prod.fst 
∘ ⇑I.subtype) → …
· 使用定理 `Subgroup.normal_goursatSnd`：∀ {G : Type u_1} {H : Type u_2} [inst : Grou
p G] [inst_1 : Group H] {I : Subgroup (G × H)},   Function.Surjective (Prod.snd 
∘ ⇑I.subtype) → …
· 使用引理 `MonoidHom.exists_mulEquiv_range_eq_graph`：exists_mulEquiv_range_eq_graph
 {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf₂ : Surjective (Prod.snd
 ∘ f)) (hf : forall g₁ g₂, (f …
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
· 使用引理 `Subgroup.mk_goursatFst_eq_iff_mk_goursatSnd_eq`：mk_goursatFst_eq_iff_mk_
goursatSnd_eq {x y : G × H} (hx : x in I) (hy : y in I) : (x.1 : G ⧸ I.goursatFs
t) = y.1 ↔ (x.2 : H ⧸ I.goursatSnd) …
-/
lemma goursat_surjective :
    have := normal_goursatFst hI₁
    have := normal_goursatSnd hI₂
    ∃ e : G ⧸ I.goursatFst ≃* H ⧸ I.goursatSnd,
      (((QuotientGroup.mk' _).prodMap (QuotientGroup.mk' _)).comp I.subtype).range =
        e.toMonoidHom.graph := by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  exact (((QuotientGroup.mk' I.goursatFst).prodMap
    (QuotientGroup.mk' I.goursatSnd)).comp I.subtype).exists_mulEquiv_range_eq_graph
    ((QuotientGroup.mk'_surjective _).comp hI₁) ((QuotientGroup.mk'_surjective _).comp hI₂)
    fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ mk_goursatFst_eq_iff_mk_goursatSnd_eq hI₁ hI₂ hx hy

/-- **Goursat's lemma** for an arbitrary subgroup.

If `I` is a subgroup of `G × H`, then there exist subgroups `G' ≤ G`, `H' ≤ H` and normal subgroups
`M ⊴ G'` and `N ⊴ H'` such that `M × N ≤ I` and the image of `I` in `G' ⧸ M × H' ⧸ N` is the graph
of an isomorphism `G' ⧸ M ≃ H' ⧸ N`. -/
@[to_additive
/-- **Goursat's lemma** for an arbitrary subgroup.

If `I` is a subgroup of `G × H`, then there exist subgroups `G' ≤ G`, `H' ≤ H` and normal subgroups
`M ≤ G'` and `N ≤ H'` such that `M × N ≤ I` and the image of `I` in `G' ⧸ M × H' ⧸ N` is the graph
of an isomorphism `G ⧸ G' ≃ H ⧸ H'`. -/]
/-
**Subgroup.goursat** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：goursat : exists (G' : Subgroup G) (H' : Subgroup H) (M : Subgroup G') (N 
: Subgroup H') (_ : M.Normal) (_ : N.Normal) (e : G' ⧸ M ≃* H' ⧸ N), I = (e.toMo
noidHom.graph.comap <| (QuotientGroup.mk' M).prodMap (QuotientGroup.mk' N)).map 
(G'.subtype.prodMap H'.subtype)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidHom.range_comp`：range_comp (g : N ->* P) (f : G ->* N) : (g.comp f
).range = f.range.map g
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `MonoidHom.fst_comp_prod`：fst_comp_prod (f : M ->* N) (g : M ->* P) : (fs
t N P).comp (f.prod g) = f
· 使用定理 `MonoidHom.subgroupMap_surjective`：subgroupMap_surjective (f : G ->* G') 
(H : Subgroup G) : Function.Surjective (f.subgroupMap H)
· 使用定理 `Subgroup.normal_goursatFst`：∀ {G : Type u_1} {H : Type u_2} [inst : Grou
p G] [inst_1 : Group H] {I : Subgroup (G × H)},   Function.Surjective (Prod.fst 
∘ ⇑I.subtype) → …
· 使用定理 `Subgroup.normal_goursatSnd`：∀ {G : Type u_1} {H : Type u_2} [inst : Grou
p G] [inst_1 : Group H] {I : Subgroup (G × H)},   Function.Surjective (Prod.snd 
∘ ⇑I.subtype) → …
· 使用引理 `Subgroup.goursat_surjective`：goursat_surjective : have
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.comap_map_eq_self`：comap_map_eq_self {f : G ->* N} {H : Subgrou
p G} (h : f.ker <= H) : comap f (map f H) = H
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Subgroup.goursatFst_prod_goursatSnd_le`：goursatFst_prod_goursatSnd_le : 
I.goursatFst.prod I.goursatSnd <= I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma goursat :
    ∃ (G' : Subgroup G) (H' : Subgroup H) (M : Subgroup G') (N : Subgroup H') (_ : M.Normal)
      (_ : N.Normal) (e : G' ⧸ M ≃* H' ⧸ N),
      I = (e.toMonoidHom.graph.comap <| (QuotientGroup.mk' M).prodMap (QuotientGroup.mk' N)).map
        (G'.subtype.prodMap H'.subtype) := by
  let G' := I.map (MonoidHom.fst ..)
  let H' := I.map (MonoidHom.snd ..)
  let P : I →* G' := (MonoidHom.fst ..).subgroupMap I
  let Q : I →* H' := (MonoidHom.snd ..).subgroupMap I
  let I' : Subgroup (G' × H') := (P.prod Q).range
  have hI₁' : Surjective (Prod.fst ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_fst, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.fst_comp_prod, MonoidHom.range_eq_top]
    exact (MonoidHom.fst ..).subgroupMap_surjective I
  have hI₂' : Surjective (Prod.snd ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_snd, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.range_eq_top]
    exact (MonoidHom.snd ..).subgroupMap_surjective I
  have := normal_goursatFst hI₁'
  have := normal_goursatSnd hI₂'
  obtain ⟨e, he⟩ := goursat_surjective hI₁' hI₂'
  refine ⟨I.map (MonoidHom.fst ..), I.map (MonoidHom.snd ..),
    I'.goursatFst, I'.goursatSnd, inferInstance, inferInstance, e, ?_⟩
  rw [← he]
  simp only [MonoidHom.range_comp, Subgroup.range_subtype, I']
  rw [comap_map_eq_self]
  · ext ⟨g, h⟩
    constructor
    · intro hgh
      simpa only [G', H', mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists,
        Prod.exists, MonoidHom.coe_prodMap, coe_subtype, Prod.mk.injEq, Prod.map_apply,
        MonoidHom.coe_snd, exists_eq_right, exists_and_right, exists_eq_right_right,
        MonoidHom.coe_fst]
        using ⟨⟨h, hgh⟩, ⟨g, hgh⟩, g, h, hgh, ⟨rfl, rfl⟩⟩
    · simp only [G', H', mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists,
        Prod.exists, MonoidHom.coe_prodMap, coe_subtype, Prod.mk.injEq, Prod.map_apply,
        MonoidHom.coe_snd, exists_eq_right, exists_and_right, exists_eq_right_right,
        MonoidHom.coe_fst, forall_exists_index, and_imp]
      rintro h₁ hgh₁ g₁ hg₁h g₂ h₂ hg₂h₂ hP hQ
      simp only [Subtype.ext_iff] at hP hQ
      rwa [← hP, ← hQ]
  · convert! goursatFst_prod_goursatSnd_le (P.prod Q).range
    ext ⟨g, h⟩
    simp_rw [G', H', MonoidHom.mem_ker, MonoidHom.coe_prodMap, Prod.map_apply, Subgroup.mem_prod,
      Prod.one_eq_mk, Prod.ext_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

end Subgroup

