/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Indecomposable elements of monoids
-/

@[expose] public section

open Set

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

/-- Given a family of elements of a monoid, a member is said to be indecomposable if it cannot be
written as a product of two others in a non-trivial way. -/
@[to_additive (attr := simp) /-- Given a family of elements of an additive monoid, a member is said
to be indecomposable if it cannot be written as a sum of two others in a non-trivial way.-/]
/-
**IsMulIndecomposable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMulIndecomposable (v : ι -> M) (s : Set ι) (i : ι) : Prop
参数：v : ι -> M；s : Set ι；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsMulIndecomposable (v : ι → M) (s : Set ι) (i : ι) : Prop :=
  i ∈ s ∧ ∀ᵉ (j ∈ s) (k ∈ s), v i = v j * v k → v j = 1 ∨ v k = 1

@[to_additive]
/-
**IsMulIndecomposable.subset** 是 Mathlib 中的一个定理，位于命名空间 `IsMulIndecomposable`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : Monoid M] (v : ι → M) (s : Set ι),
 {i | IsMulIndecomposable v s i} ⊆ s
参数：v : ι → M；s : Set ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
protected lemma IsMulIndecomposable.subset (v : ι → M) (s : Set ι) :
    {i | IsMulIndecomposable v s i} ⊆ s := by
  aesop

@[to_additive]
/-
**isMulIndecomposable_id_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulIndecomposable_id_univ [Subsingleton Mˣ] {x : M} (hx : x != 1) : IsMu
lIndecomposable id univ x ↔ Irreducible x
参数：hx : x != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
-/
lemma isMulIndecomposable_id_univ [Subsingleton Mˣ] {x : M} (hx : x ≠ 1) :
    IsMulIndecomposable id univ x ↔ Irreducible x :=
  ⟨fun h ↦ ⟨by simpa, by simpa using h⟩, fun h ↦ by simpa using h.isUnit_or_isUnit⟩

/-- The "base" of a set of points of a monoid relative to a morphism `f`. -/
@[to_additive /-- The "base" of `v` relative to a morphism `f`.

In the case that `v` is the set of roots of a crystallographic root system, and `S = ℚ`, this is the
base of the root system associated to `f`. -/]
/-
**IsMulIndecomposable.baseOf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMulIndecomposable.baseOf [Monoid S] (v : ι -> M) (f : M ->* S) : Set ι
参数：v : ι -> M；f : M ->* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsMulIndecomposable.baseOf [Monoid S] (v : ι → M) (f : M →* S) : Set ι :=
  {j | IsMulIndecomposable v {i | 1 < f (v i)} j}

@[to_additive]
/-
**IsMulIndecomposable.baseOf_subset_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulIndecomposable.baseOf_subset_one_lt [Monoid S] (v : ι -> M) (f : M ->
* S) : IsMulIndecomposable.baseOf v f subseteq {i | 1 < f (v i)}
参数：v : ι -> M；f : M ->* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulIndecomposable.subset`：∀ {ι : Type u_1} {M : Type u_2} [inst : Mono
id M] (v : ι → M) (s : Set ι), {i | IsMulIndecomposable v s i} ⊆ s
-/
lemma IsMulIndecomposable.baseOf_subset_one_lt [Monoid S] (v : ι → M) (f : M →* S) :
    IsMulIndecomposable.baseOf v f ⊆ {i | 1 < f (v i)} :=
  IsMulIndecomposable.subset _ _

@[to_additive]
/-
**IsMulIndecomposable.image_baseOf_inv_comp_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulIndecomposable.image_baseOf_inv_comp_eq [InvolutiveInv ι] [CommGroup 
S] [IsOrderedMonoid S] (v : ι -> G) (hv_inv : forall i, v i⁻¹ = (v i)⁻¹) (f : G 
->* S) : v '' baseOf v (invMonoidHom.comp f) = (invMonoidHom ∘ v) '' baseOf v f
参数：v : ι -> G；hv_inv : forall i, v i⁻¹ = (v i)⁻¹；f : G ->* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `invMonoidHom_comp_invMonoidHom`：invMonoidHom_comp_invMonoidHom : (invMon
oidHom (α
· 使用定理 `MonoidHom.coe_comp`：MonoidHom.coe_comp [MulOne M] [MulOne N] [MulOne P] 
(g : N ->* P) (f : M ->* N) : ↑(g.comp f) = g ∘ f
· 使用定理 `MonoidHom.id_comp`：MonoidHom.id_comp [MulOne M] [MulOne N] (f : M ->* N)
 : (MonoidHom.id N).comp f = f
· 使用定理 `MonoidHom.comp_assoc`：MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOn
e N] [MulOne P] [MulOne Q] (f : M ->* N) (g : N ->* P) (h : P ->* Q) : (h.comp g
).comp f =…
-/
lemma IsMulIndecomposable.image_baseOf_inv_comp_eq [InvolutiveInv ι]
    [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) :
    v '' baseOf v (invMonoidHom.comp f) = (invMonoidHom ∘ v) '' baseOf v f := by
  suffices ∀ (f : G →* S),
      v '' baseOf v (invMonoidHom.comp f) ⊆ (invMonoidHom ∘ v) '' baseOf v f by
    apply subset_antisymm (this f)
    replace this := image_mono (f := invMonoidHom) <| this (invMonoidHom.comp f)
    rw [← MonoidHom.comp_assoc, invMonoidHom_comp_invMonoidHom, MonoidHom.id_comp, image_comp,
      ← image_comp invMonoidHom invMonoidHom, ← MonoidHom.coe_comp, invMonoidHom_comp_invMonoidHom,
      ← image_comp] at this
    simpa using this
  clear f
  rintro f g ⟨i, ⟨hi, hi'⟩, rfl⟩
  refine ⟨i⁻¹, ⟨by simpa [hv_inv] using hi, fun j hj k hk hi ↦ ?_⟩, by simp [hv_inv]⟩
  replace hi : v i = v j⁻¹ * v k⁻¹ := by
    rwa [hv_inv, inv_eq_iff_eq_inv, mul_inv, ← hv_inv, ← hv_inv] at hi
  specialize hi' j⁻¹ (by simpa [hv_inv]) k⁻¹ (by simpa [hv_inv]) hi
  aesop

/-- Given a finite family of points `v` in a monoid `M`, together with a morphism into a
linearly-ordered monoid `f : M →* S`, the submonoid generated by those points of `v` which lie in
the "half space" where `f > 1` is generated by the subset of such points which are indecomposable
with respect to points in this half space. -/
@[to_additive /-- Given a finite family of points `v` in an additive monoid `M`, together with a
morphism into a linearly-ordered additive monoid `f : M →+ S`, the submonoid generated by those
points of `v` which lie in the half space where `f > 0` is generated by the subset of such points
which are indecomposable with respect to points in this half space.

If `v` is the set of roots of a crystallographic root system and `S = ℚ`, then this is
[serre1965](Ch. V, §9, Lemma 2) and it may be used to prove that the root system has a base. -/]
/-
**Submonoid.closure_image_isMulIndecomposable_baseOf** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：Submonoid.closure_image_isMulIndecomposable_baseOf [Finite ι] [CommMonoid 
S] [IsOrderedCancelMonoid S] (v : ι -> M) (f : M ->* S) : closure (v '' IsMulInd
ecomposable.baseOf v f) = closure (v '' {i | 1 < f (v i)})
参数：v : ι -> M；f : M ->* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submonoid.closure_mono`：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : 
closure s <= closure t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用引理 `IsMulIndecomposable.baseOf_subset_one_lt`：IsMulIndecomposable.baseOf_sub
set_one_lt [Monoid S] (v : ι -> M) (f : M ->* S) : IsMulIndecomposable.baseOf v 
f subseteq {i | 1 < f (v i)}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Finite.exists_minimalFor`：∀ {ι : Type u_1} {α : Type u_2} [inst : LE
 α] [IsTrans α fun a a_1 => a_1 ≤ a] (f : ι → α) (s : Set ι),   s.Finite → s.Non
empty → ∃ i, Minim…
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `MinimalFor.prop`：MinimalFor.prop (h : MinimalFor P f i) : P i
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `MinimalFor.le_of_le`：MinimalFor.le_of_le (h : MinimalFor P f i) (hj : P 
j) (hji : f j <= f i) : f i <= f j
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toIsCancelMul`：∀ {α : Type u_1} [inst : CommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], IsCancelMul α
（共 34 条，此处仅展示前 30 条）
-/
lemma Submonoid.closure_image_isMulIndecomposable_baseOf [Finite ι]
    [CommMonoid S] [IsOrderedCancelMonoid S]
    (v : ι → M) (f : M →* S) :
    closure (v '' IsMulIndecomposable.baseOf v f) = closure (v '' {i | 1 < f (v i)}) := by
  refine le_antisymm (closure_mono (image_mono <| IsMulIndecomposable.baseOf_subset_one_lt v f))
    (closure_le.mpr ?_)
  rintro - ⟨i, hi : 1 < f (v i), rfl⟩
  by_contra hi'
  let t : Set ι := {i | IsMulIndecomposable v {j | 1 < f (v j)} i}
  let s : Set ι := {j | 1 < f (v j) ∧ v j ∉ closure (v '' t)}
  have hne : s.Nonempty := ⟨i, hi, hi'⟩
  clear! i
  obtain ⟨i, hi⟩ := s.toFinite.exists_minimalFor (f ∘ v) s hne
  have ⟨(hi₀ : 1 < f (v i)), (hi₁ : v i ∉ _)⟩ : i ∈ s := hi.prop
  have hi₂ (k : ι) (hk₀ : 1 < f (v k)) (hk₁ : f (v k) < f (v i)) : v k ∈ closure (v '' t) := by
    by_contra hk₂; exact not_le.mpr hk₁ <| hi.le_of_le ⟨hk₀, hk₂⟩ hk₁.le
  have hi₃ : i ∉ t := by contrapose hi₁; exact subset_closure <| mem_image_of_mem v hi₁
  obtain ⟨j, k, hj, hk, hjk⟩ : ∃ (j k : ι) (hj : 1 < f (v j)) (hk : 1 < f (v k)),
      v i = v j * v k := by
    grind [IsMulIndecomposable]
  have hj' : v j ∈ closure (v '' t) := hi₂ j hj <| by aesop
  have hk' : v k ∈ closure (v '' t) := hi₂ k hk <| by aesop
  replace hjk : v i ∈ closure (v '' t) := hjk ▸ mul_mem hj' hk'
  exact hi₁ hjk

@[to_additive]
/-
**Subgroup.closure_image_isMulIndecomposable_baseOf** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Subgroup.closure_image_isMulIndecomposable_baseOf [Finite ι] [InvolutiveIn
v ι] [CommGroup S] [IsOrderedMonoid S] (v : ι -> G) (hv_inv : forall i, v i⁻¹ = 
(v i)⁻¹) (f : G ->* S) (hf : forall i, f (v i) != 1) : closure (v '' IsMulIndeco
mposable.baseOf v f) = closure (range v)
参数：v : ι -> G；hv_inv : forall i, v i⁻¹ = (v i)⁻¹；f : G ->* S；hf : forall i, f (v
 i) != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.closure_mono`：closure_mono ⦃h k : Set G⦄ (h' : h subseteq k) : 
closure h <= closure k
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Submonoid.closure_image_isMulIndecomposable_baseOf`：Submonoid.closure_im
age_isMulIndecomposable_baseOf [Finite ι] [CommMonoid S] [IsOrderedCancelMonoid 
S] (v : ι -> M) (f : M ->* S) : closure …
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `Subgroup.le_closure_toSubmonoid`：le_closure_toSubmonoid (S : Set G) : Su
bmonoid.closure S <= (closure S).toSubmonoid
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用引理 `IsMulIndecomposable.image_baseOf_inv_comp_eq`：IsMulIndecomposable.image_
baseOf_inv_comp_eq [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S] (v : ι ->
 G) (hv_inv : forall i, v i⁻¹ = (v…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Involutive.comp_self`：comp_self : f ∘ f = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.image_id_eq`：image_id_eq : image (id : α -> α) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 35 条，此处仅展示前 30 条）
-/
lemma Subgroup.closure_image_isMulIndecomposable_baseOf [Finite ι] [InvolutiveInv ι]
    [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) (hf : ∀ i, f (v i) ≠ 1) :
    closure (v '' IsMulIndecomposable.baseOf v f) = closure (range v) := by
  rw [← image_univ]
  refine le_antisymm (closure_mono (image_mono <| by simp)) ((closure_le _).mpr ?_)
  have : univ = {i | 1 < f (v i)} ∪ {i | f (v i) < 1} := by ext i; simp [(hf i).symm]
  rw [this, image_union, union_subset_iff]
  refine ⟨le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f)), ?_⟩
  · simp [Submonoid.closure_image_isMulIndecomposable_baseOf]
  · let f' : G →* S := invMonoidHom.comp f
    have h₁ : (invMonoidHom ∘ v) '' IsMulIndecomposable.baseOf v f' =
        v '' IsMulIndecomposable.baseOf v f := by
      rw [image_comp, IsMulIndecomposable.image_baseOf_inv_comp_eq v hv_inv f, image_comp,
        ← image_comp]
      simp
    have h₂ : v '' {i | f (v i) < 1} = v '' {i | 1 < f' (v i)} := by simp [f']
    rw [h₂, ← h₁, image_comp, coe_invMonoidHom, image_inv_eq_inv, closure_inv]
    refine le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f'))
    simp [Submonoid.closure_image_isMulIndecomposable_baseOf]

namespace IsMulIndecomposable

@[to_additive]
/-
**IsMulIndecomposable.pairwise_div_notMem_range** 是 Mathlib 中的一个引理，位于命名空间 `IsMul
Indecomposable`。
形式化陈述：pairwise_div_notMem_range [InvolutiveInv ι] (v : ι -> G) (hv_one : forall 
i, v i != 1) (hv_inv : forall i, v i⁻¹ = (v i)⁻¹) (s t : Set ι) (hst : s subsete
q {i | IsMulIndecomposable v t i}) (hv_t : forall i, i in t ∨ i⁻¹ in t) : s.Pair
wise fun i j => v i / v j ∉ range v
参数：v : ι -> G；hv_one : forall i, v i != 1；hv_inv : forall i, v i⁻¹ = (v i)⁻¹；s t
 : Set ι；hst : s subseteq {i | IsMulIndecomposable v t i}；hv_t : forall i, i in 
t ∨ i⁻¹ in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsMulIndecomposable.subset`：∀ {ι : Type u_1} {M : Type u_2} [inst : Mono
id M] (v : ι → M) (s : Set ι), {i | IsMulIndecomposable v s i} ⊆ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
lemma pairwise_div_notMem_range [InvolutiveInv ι]
    (v : ι → G)
    (hv_one : ∀ i, v i ≠ 1)
    (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (s t : Set ι)
    (hst : s ⊆ {i | IsMulIndecomposable v t i})
    (hv_t : ∀ i, i ∈ t ∨ i⁻¹ ∈ t) :
    s.Pairwise fun i j ↦ v i / v j ∉ range v := by
  have h_sub : s ⊆ t := hst.trans (IsMulIndecomposable.subset _ _)
  intro i hi j hj hne
  by_contra! ⟨k, hk⟩
  rcases hv_t k with hk' | hk'
  · suffices ¬ IsMulIndecomposable v t i from this (hst hi)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ ↦ ⟨k, hk', j, h_sub hj, by simp [hk]⟩
  · suffices ¬ IsMulIndecomposable v t j from this (hst hj)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ ↦ ⟨k⁻¹, hk', i, h_sub hi, by simp [hv_inv, hk]⟩

@[to_additive]
/-
**IsMulIndecomposable.pairwise_div_notMem_range'** 是 Mathlib 中的一个引理，位于命名空间 `IsMu
lIndecomposable`。
形式化陈述：pairwise_div_notMem_range' [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoi
d S] (v : ι -> G) (hv_inv : forall i, v i⁻¹ = (v i)⁻¹) (f : G ->* S) (hf : foral
l i, f (v i) != 1) (s : Set ι) (hst : s subseteq {j | IsMulIndecomposable v {i |
 1 < f (v i)} j}) : s.Pairwise fun i j => v i / v j ∉ range v
参数：v : ι -> G；hv_inv : forall i, v i⁻¹ = (v i)⁻¹；f : G ->* S；hf : forall i, f (v
 i) != 1；s : Set ι；hst : s subseteq {j | IsMulIndecomposable v {i | 1 < f (v i)}
 j}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsMulIndecomposable.pairwise_div_notMem_range`：pairwise_div_notMem_range
 [InvolutiveInv ι] (v : ι -> G) (hv_one : forall i, v i != 1) (hv_inv : forall i
, v i⁻¹ = (v i)⁻¹) (s t : Set ι) (h…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma pairwise_div_notMem_range' [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) (hf : ∀ i, f (v i) ≠ 1)
    (s : Set ι) (hst : s ⊆ {j | IsMulIndecomposable v {i | 1 < f (v i)} j}) :
    s.Pairwise fun i j ↦ v i / v j ∉ range v := by
  have hv_one : ∀ i, v i ≠ 1 := fun i ↦ by contrapose! hf; exact ⟨i, by simp [hf]⟩
  apply pairwise_div_notMem_range v hv_one hv_inv s {i | 1 < f (v i)} hst fun i ↦ ?_
  simpa [hv_inv] using (hf i).symm

@[to_additive]
/-
**IsMulIndecomposable.pairwise_baseOf_div_notMem** 是 Mathlib 中的一个引理，位于命名空间 `IsMu
lIndecomposable`。
形式化陈述：pairwise_baseOf_div_notMem [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoi
d S] (v : ι -> G) (hv_inv : forall i, v i⁻¹ = (v i)⁻¹) (f : G ->* S) (hf : foral
l i, f (v i) != 1) : (baseOf v f).Pairwise fun i j => v i / v j ∉ range v
参数：v : ι -> G；hv_inv : forall i, v i⁻¹ = (v i)⁻¹；f : G ->* S；hf : forall i, f (v
 i) != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMulIndecomposable.pairwise_div_notMem_range'`：pairwise_div_notMem_rang
e' [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S] (v : ι -> G) (hv_inv : fo
rall i, v i⁻¹ = (v i)⁻¹) (f : G ->* …
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
lemma pairwise_baseOf_div_notMem [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) (hf : ∀ i, f (v i) ≠ 1) :
    (baseOf v f).Pairwise fun i j ↦ v i / v j ∉ range v :=
  pairwise_div_notMem_range' v hv_inv f hf (baseOf v f) (.refl _)

set_option linter.style.whitespace false in -- manual alignment is not recognised
@[to_additive]
/-
**IsMulIndecomposable.mem_or_inv_mem_closure_baseOf** 是 Mathlib 中的一个引理，位于命名空间 `I
sMulIndecomposable`。
形式化陈述：mem_or_inv_mem_closure_baseOf [Finite ι] [InvolutiveInv ι] [CommGroup S] [
IsOrderedMonoid S] (v : ι -> G) (f : G ->* S) (i : ι) (hi : f (v i) != 1) (hi' :
 v i⁻¹ = (v i)⁻¹) : v i in Submonoid.closure (v '' baseOf v f) ∨ (v i)⁻¹ in Subm
onoid.closure (v '' baseOf v f)
参数：v : ι -> G；f : G ->* S；i : ι；hi : f (v i) != 1；hi' : v i⁻¹ = (v i)⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submonoid.closure_image_isMulIndecomposable_baseOf`：Submonoid.closure_im
age_isMulIndecomposable_baseOf [Finite ι] [CommMonoid S] [IsOrderedCancelMonoid 
S] (v : ι -> M) (f : M ->* S) : closure …
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma mem_or_inv_mem_closure_baseOf [Finite ι] [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G)
    (f : G →* S) (i : ι) (hi : f (v i) ≠ 1) (hi' : v i⁻¹ = (v i)⁻¹) :
     v i    ∈ Submonoid.closure (v '' baseOf v f) ∨
    (v i)⁻¹ ∈ Submonoid.closure (v '' baseOf v f) := by
  rw [Submonoid.closure_image_isMulIndecomposable_baseOf v f]
  rcases lt_or_gt_of_ne hi with hj | hj
  · right
    exact Submonoid.subset_closure ⟨i⁻¹, by simpa [hi']⟩
  · left
    exact Submonoid.subset_closure ⟨i, by simpa⟩

end IsMulIndecomposable

@[to_additive]
/-
**Submonoid.mem_closure_image_one_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.mem_closure_image_one_lt_iff [CommMonoid S] [IsOrderedCancelMono
id S] (v : ι -> M) (f : M ->* S) (i : ι) (hv_one : v i != 1) : v i in closure (v
 '' {i | 1 < f (v i)}) ↔ 1 < f (v i)
参数：v : ι -> M；f : M ->* S；i : ι；hv_one : v i != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Left.one_lt_mul`：Left.one_lt_mul [MulLeftStrictMono α] {a b : α} (ha : 1
 < a) (hb : 1 < b) : 1 < a * b
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma Submonoid.mem_closure_image_one_lt_iff [CommMonoid S] [IsOrderedCancelMonoid S]
    (v : ι → M) (f : M →* S) (i : ι) (hv_one : v i ≠ 1) :
    v i ∈ closure (v '' {i | 1 < f (v i)}) ↔ 1 < f (v i) := by
  refine ⟨fun hi ↦ ?_, fun hi ↦ subset_closure <| mem_image_of_mem v hi⟩
  suffices v i = 1 ∨ 1 < f (v i) from this.resolve_left hv_one
  refine closure_induction (by grind) (by simp) (fun x y _ _ hx hy ↦ ?_) hi
  rcases hx with rfl | hx; · simpa
  rcases hy with rfl | hy; · right; simpa
  right
  simpa only [map_mul] using Left.one_lt_mul hx hy

@[to_additive]
/-
**Submonoid.apply_ne_one_of_mem_or_inv_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.apply_ne_one_of_mem_or_inv_mem_closure [InvolutiveInv ι] [CommGr
oup S] [IsOrderedMonoid S] (v : ι -> G) (f : G ->* S) (s : Set ι) (hf : forall i
 in s, 1 < f (v i)) (i : ι) (hv_one : v i != 1) (hv_inv : v i⁻¹ = (v i)⁻¹) (hsp 
: v i in closure (v '' s) ∨ (v i)⁻¹ in closure (v '' s)) : f (v i) != 1
参数：v : ι -> G；f : G ->* S；s : Set ι；hf : forall i in s, 1 < f (v i)；i : ι；hv_one
 : v i != 1；hv_inv : v i⁻¹ = (v i)⁻¹；hsp : v i in closure (v '' s) ∨ (v i)⁻¹ in 
closure (v '' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `lt_mul_of_lt_of_one_lt`：lt_mul_of_lt_of_one_lt [MulLeftStrictMono α] {a 
b c : α} (hbc : b < c) (ha : 1 < a) : b < c * a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma Submonoid.apply_ne_one_of_mem_or_inv_mem_closure
    [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G)
    (f : G →* S)
    (s : Set ι)
    (hf : ∀ i ∈ s, 1 < f (v i))
    (i : ι) (hv_one : v i ≠ 1) (hv_inv : v i⁻¹ = (v i)⁻¹)
    (hsp : v i ∈ closure (v '' s) ∨ (v i)⁻¹ ∈ closure (v '' s)) :
    f (v i) ≠ 1 := by
  wlog hi : v i ∈ closure (v '' s)
  · rcases hsp with hi' | hi'; · contradiction
    simpa [hv_inv] using this v f s hf i⁻¹ (by simpa [hv_inv]) (by simp [hv_inv])
      (by left; simpa [hv_inv]) (by simpa [hv_inv])
  suffices v i ≠ 1 → 1 < f (v i) from (this hv_one).ne'
  refine closure_induction (by simp_all) (by simp) (fun x y _ _ hx hy _ ↦ ?_) hi
  rcases eq_or_ne x 1 with rfl | hx'; · grind
  rcases eq_or_ne y 1 with rfl | hy'; · grind
  simpa using lt_mul_of_lt_of_one_lt (hx hx') (hy hy')

open Submonoid in
@[to_additive]
/-
**IsMulIndecomposable.apply_ne_one_iff_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulIndecomposable.apply_ne_one_iff_mem_closure [Finite ι] [InvolutiveInv
 ι] [CommGroup S] [IsOrderedMonoid S] (v : ι -> G) (f : G ->* S) (i : ι) (hi : v
 i != 1) (hi' : v i⁻¹ = (v i)⁻¹) : f (v i) != 1 ↔ v i in closure (v '' baseOf v 
f) ∨ (v i)⁻¹ in closure (v '' baseOf v f)
参数：v : ι -> G；f : G ->* S；i : ι；hi : v i != 1；hi' : v i⁻¹ = (v i)⁻¹。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMulIndecomposable.mem_or_inv_mem_closure_baseOf`：mem_or_inv_mem_closur
e_baseOf [Finite ι] [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S] (v : ι -
> G) (f : G ->* S) (i : ι) (hi : f (v i…
· 使用引理 `Submonoid.apply_ne_one_of_mem_or_inv_mem_closure`：Submonoid.apply_ne_one
_of_mem_or_inv_mem_closure [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S] (
v : ι -> G) (f : G ->* S) (s : Set ι) …
· 使用引理 `IsMulIndecomposable.baseOf_subset_one_lt`：IsMulIndecomposable.baseOf_sub
set_one_lt [Monoid S] (v : ι -> M) (f : M ->* S) : IsMulIndecomposable.baseOf v 
f subseteq {i | 1 < f (v i)}
-/
lemma IsMulIndecomposable.apply_ne_one_iff_mem_closure
    [Finite ι] [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (f : G →* S) (i : ι) (hi : v i ≠ 1) (hi' : v i⁻¹ = (v i)⁻¹) :
    f (v i) ≠ 1 ↔ v i ∈ closure (v '' baseOf v f) ∨ (v i)⁻¹ ∈ closure (v '' baseOf v f) :=
  ⟨fun h ↦ mem_or_inv_mem_closure_baseOf v f i h hi',
    apply_ne_one_of_mem_or_inv_mem_closure v f (baseOf v f) (baseOf_subset_one_lt v f) i hi hi'⟩
