/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Basic properties of group actions

This file primarily concerns itself with orbits, stabilizers, and other objects defined in terms of
actions. Despite this file being called `basic`, low-level helper lemmas for algebraic manipulation
of `•` belong elsewhere.

## Main definitions

* `MulAction.orbit`
* `MulAction.fixedPoints`
* `MulAction.fixedBy`
* `MulAction.stabilizer`

-/

@[expose] public section


universe u v

open Function Module
open scoped Pointwise

namespace MulAction

variable (M : Type u) [Monoid M] (α : Type v) [MulAction M α] {β : Type*} [MulAction M β]

section Orbit

variable {α M}

@[to_additive]
/-
**MulAction.fst_mem_orbit_of_mem_orbit** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：fst_mem_orbit_of_mem_orbit {x y : α × β} (h : x in MulAction.orbit M y) : 
x.1 in MulAction.orbit M y.1
参数：h : x in MulAction.orbit M y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
-/
lemma fst_mem_orbit_of_mem_orbit {x y : α × β} (h : x ∈ MulAction.orbit M y) :
    x.1 ∈ MulAction.orbit M y.1 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
/-
**MulAction.snd_mem_orbit_of_mem_orbit** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：snd_mem_orbit_of_mem_orbit {x y : α × β} (h : x in MulAction.orbit M y) : 
x.2 in MulAction.orbit M y.2
参数：h : x in MulAction.orbit M y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
-/
lemma snd_mem_orbit_of_mem_orbit {x y : α × β} (h : x ∈ MulAction.orbit M y) :
    x.2 ∈ MulAction.orbit M y.2 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
/-
**MulAction._root_.Finite.finite_mulAction_orbit** 是 Mathlib 中的一个引理，位于命名空间 `MulA
ction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finite.finite_mulAction_orbit [Finite M] (a : α) : Set.Finite (orbit M a) :=
  Set.finite_range _

variable (M)

@[to_additive]
/-
**MulAction.orbit_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：orbit_eq_univ [IsPretransitive M α] (a : α) : orbit M a = Set.univ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用引理 `MulAction.surjective_smul`：surjective_smul (x : α) : Surjective fun c : 
M => c • x
-/
theorem orbit_eq_univ [IsPretransitive M α] (a : α) : orbit M a = Set.univ :=
  (surjective_smul M a).range_eq

end Orbit

section FixedPoints

variable {M α}

@[to_additive (attr := simp)]
/-
**MulAction.subsingleton_orbit_iff_mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `Mu
lAction`。
形式化陈述：subsingleton_orbit_iff_mem_fixedPoints {a : α} : (orbit M a).Subsingleton 
↔ a in fixedPoints M α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_fixedPoints`：mem_fixedPoints {a : α} : a in fixedPoints M 
α ↔ forall m : M, m • a = a
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
· 使用定理 `MulAction.mem_orbit_self`：mem_orbit_self (a : α) : a in orbit M a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subsingleton_orbit_iff_mem_fixedPoints {a : α} :
    (orbit M a).Subsingleton ↔ a ∈ fixedPoints M α := by
  rw [mem_fixedPoints]
  constructor
  · exact fun h m ↦ h (mem_orbit a m) (mem_orbit_self a)
  · rintro h _ ⟨m, rfl⟩ y ⟨p, rfl⟩
    simp only [h]

@[to_additive mem_fixedPoints_iff_card_orbit_eq_one]
/-
**MulAction.mem_fixedPoints_iff_card_orbit_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Mul
Action`。
形式化陈述：mem_fixedPoints_iff_card_orbit_eq_one {a : α} [Fintype (orbit M a)] : a in
 fixedPoints M α ↔ Fintype.card (orbit M a) = 1
参数：orbit M a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mem_fixedPoints_iff_card_orbit_eq_one {a : α} [Fintype (orbit M a)] :
    a ∈ fixedPoints M α ↔ Fintype.card (orbit M a) = 1 := by
  simp only [← subsingleton_orbit_iff_mem_fixedPoints, le_antisymm_iff,
    Fintype.card_le_one_iff_subsingleton, Nat.add_one_le_iff, Fintype.card_pos_iff,
    Set.subsingleton_coe, iff_self_and, Set.nonempty_coe_sort, nonempty_orbit, implies_true]

@[to_additive instDecidablePredMemSetFixedByAddOfDecidableEq]
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (m : M) [DecidableEq β] :
    DecidablePred fun b : β => b ∈ MulAction.fixedBy β m := fun b ↦ by
  simp only [MulAction.mem_fixedBy]
  infer_instance

end FixedPoints

end MulAction

/-- `smul` by a `k : M` over a group is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `IsSMulRegular`.
The typeclass that restricts all terms of `M` to have this property is `Module.IsTorsionFree`. -/
/-
**smul_cancel_of_non_zero_divisor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_cancel_of_non_zero_divisor {M G : Type*} [Monoid M] [AddGroup G] [Dis
tribMulAction M G] (k : M) (h : forall x : G, k • x = 0 -> x = 0) {a b : G} (h' 
: k • a = k • b) : a = b
参数：k : M；h : forall x : G, k • x = 0 -> x = 0；h' : k • a = k • b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
`smul` by a `k : M` over a group is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `IsSMulRegular`.
The typeclass that restricts all terms of `M` to have this property is `Module.I
sTorsionFree`.
-/
theorem smul_cancel_of_non_zero_divisor {M G : Type*} [Monoid M] [AddGroup G]
    [DistribMulAction M G] (k : M) (h : ∀ x : G, k • x = 0 → x = 0) {a b : G} (h' : k • a = k • b) :
    a = b := by
  rw [← sub_eq_zero]
  refine h _ ?_
  rw [smul_sub, h', sub_self]

namespace MulAction
variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

/-
**MulAction.fixedPoints_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
[Subsingleton α],   MulAction.fixedPoints G α = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
@[to_additive] theorem fixedPoints_of_subsingleton [Subsingleton α] :
    fixedPoints G α = .univ := by
  apply Set.eq_univ_of_forall
  simp only [mem_fixedPoints]
  intro x hx
  apply Subsingleton.elim ..

/-- If a group acts nontrivially, then the type is nontrivial -/
@[to_additive /-- If a subgroup acts nontrivially, then the type is nontrivial. -/]
/-
**MulAction.nontrivial_of_fixedPoints_ne_univ** 是 Mathlib 中的一个定理，位于命名空间 `MulActi
on`。
形式化陈述：nontrivial_of_fixedPoints_ne_univ (h : fixedPoints G α != .univ) : Nontriv
ial α
参数：h : fixedPoints G α != .univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `MulAction.fixedPoints_of_subsingleton`：∀ {G : Type u_1} {α : Type u_2} [
inst : Group G] [inst_1 : MulAction G α] [Subsingleton α],   MulAction.fixedPoin
ts G α = Set.univ

--- 原说明 ---
If a group acts nontrivially, then the type is nontrivial
-/
theorem nontrivial_of_fixedPoints_ne_univ (h : fixedPoints G α ≠ .univ) :
    Nontrivial α :=
  (subsingleton_or_nontrivial α).resolve_left fun _ ↦ h fixedPoints_of_subsingleton

section Orbit

-- TODO: This proof is redoing a special case of `MulAction.IsInvariantBlock.isBlock`. Can we move
-- this lemma earlier to golf?
@[to_additive (attr := simp)]
/-
**MulAction.smul_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：smul_orbit (g : G) (a : α) : g • orbit G a = orbit G a
参数：g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MulAction.smul_orbit_subset`：smul_orbit_subset (m : M) (a : α) : m • orb
it M a subseteq orbit M a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem smul_orbit (g : G) (a : α) : g • orbit G a = orbit G a :=
  (smul_orbit_subset g a).antisymm <|
    calc
      orbit G a = g • g⁻¹ • orbit G a := (smul_inv_smul _ _).symm
      _ ⊆ g • orbit G a := Set.image_mono (smul_orbit_subset _ _)

/-- The action of a group on an orbit is transitive. -/
@[to_additive /-- The action of an additive group on an orbit is transitive. -/]
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of a group on an orbit is transitive.
-/
instance (a : α) : IsPretransitive G (orbit G a) :=
  ⟨by
    rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
    use h * g⁻¹
    ext1
    simp [mul_smul]⟩

@[to_additive]
/-
**MulAction.orbitRel_subgroup_le** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：orbitRel_subgroup_le (H : Subgroup G) : orbitRel H α <= orbitRel G α
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Setoid.le_def`：le_def {r s : Setoid α} : r <= s ↔ forall {x y}, r x y ->
 s x y
· 使用引理 `MulAction.mem_orbit_of_mem_orbit_subgroup`：mem_orbit_of_mem_orbit_subgro
up {H : Subgroup G} {a b : α} (h : a in orbit H b) : a in orbit G b
-/
lemma orbitRel_subgroup_le (H : Subgroup G) : orbitRel H α ≤ orbitRel G α :=
  Setoid.le_def.2 mem_orbit_of_mem_orbit_subgroup

@[to_additive]
/-
**MulAction.orbitRel_subgroupOf** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：orbitRel_subgroupOf (H K : Subgroup G) : orbitRel (H.subgroupOf K) α = orb
itRel (H ⊓ K : Subgroup G) α
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.subgroupOf_map_subtype`：subgroupOf_map_subtype (H K : Subgroup 
G) : (H.subgroupOf K).map K.subtype = H ⊓ K
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma orbitRel_subgroupOf (H K : Subgroup G) :
    orbitRel (H.subgroupOf K) α = orbitRel (H ⊓ K : Subgroup G) α := by
  rw [← Subgroup.subgroupOf_map_subtype]
  ext x
  simp_rw [orbitRel_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only
    refine mem_orbit _ (⟨gv, ?_⟩ : Subgroup.map K.subtype (H.subgroupOf K))
    simpa using! gp
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only
    simp only [Subgroup.subgroupOf_map_subtype, Subgroup.mem_inf] at gp
    refine mem_orbit _ (⟨⟨gv, ?_⟩, ?_⟩ : H.subgroupOf K)
    · exact gp.2
    · simp only [Subgroup.mem_subgroupOf]
      exact gp.1

variable (G α)

/-- An action is pretransitive if and only if the quotient by `MulAction.orbitRel` is a
subsingleton. -/
@[to_additive /-- An additive action is pretransitive if and only if the quotient by
`AddAction.orbitRel` is a subsingleton. -/]
/-
**MulAction.pretransitive_iff_subsingleton_quotient** 是 Mathlib 中的一个定理，位于命名空间 `M
ulAction`。
形式化陈述：pretransitive_iff_subsingleton_quotient : IsPretransitive G α ↔ Subsinglet
on (orbitRel.Quotient G α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem pretransitive_iff_subsingleton_quotient :
    IsPretransitive G α ↔ Subsingleton (orbitRel.Quotient G α) := by
  refine ⟨fun _ ↦ ⟨fun a b ↦ ?_⟩, fun _ ↦ ⟨fun a b ↦ ?_⟩⟩
  · refine Quot.inductionOn a (fun x ↦ ?_)
    exact Quot.inductionOn b (fun y ↦ Quot.sound <| exists_smul_eq G y x)
  · have h : Quotient.mk (orbitRel G α) b = ⟦a⟧ := Subsingleton.elim _ _
    exact Quotient.eq''.mp h

/-- If `α` is non-empty, an action is pretransitive if and only if the quotient has exactly one
element. -/
@[to_additive /-- If `α` is non-empty, an additive action is pretransitive if and only if the
quotient has exactly one element. -/]
/-
**MulAction.pretransitive_iff_unique_quotient_of_nonempty** 是 Mathlib 中的一个定理，位于命
名空间 `MulAction`。
形式化陈述：pretransitive_iff_unique_quotient_of_nonempty [Nonempty α] : IsPretransiti
ve G α ↔ Nonempty (Unique <| orbitRel.Quotient G α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `unique_iff_subsingleton_and_nonempty`：unique_iff_subsingleton_and_nonemp
ty (α : Sort u) : Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α
· 使用定理 `MulAction.pretransitive_iff_subsingleton_quotient`：pretransitive_iff_sub
singleton_quotient : IsPretransitive G α ↔ Subsingleton (orbitRel.Quotient G α)
· 使用定理 `iff_self_and`：∀ {p q : Prop}, (p ↔ p ∧ q) ↔ p → q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_quotient_iff`：nonempty_quotient_iff (s : Setoid α) : Nonempty (
Quotient s) ↔ Nonempty α
-/
theorem pretransitive_iff_unique_quotient_of_nonempty [Nonempty α] :
    IsPretransitive G α ↔ Nonempty (Unique <| orbitRel.Quotient G α) := by
  rw [unique_iff_subsingleton_and_nonempty, pretransitive_iff_subsingleton_quotient, iff_self_and]
  exact fun _ ↦ (nonempty_quotient_iff _).mpr inferInstance

variable {G α}

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : orbitRel.Quotient G α) : IsPretransitive G x.orbit where
  exists_smul_eq := by
    induction x using Quotient.inductionOn'
    rintro ⟨y, yh⟩ ⟨z, zh⟩
    rw [orbitRel.Quotient.mem_orbit, Quotient.eq''] at yh zh
    rcases yh with ⟨g, rfl⟩
    rcases zh with ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    ext
    simp [mul_smul]

variable (G) (α)

local notation "Ω" => orbitRel.Quotient G α

@[to_additive]
/-
**MulAction._root_.Finite.of_finite_mulAction_orbitRel_quotient** 是 Mathlib 中的一个
引理，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finite.of_finite_mulAction_orbitRel_quotient [Finite G] [Finite Ω] : Finite α := by
  rw [(selfEquivSigmaOrbits' G _).finite_iff]
  have : ∀ g : Ω, Finite g.orbit := by
    intro g
    induction g using Quotient.inductionOn'
    simpa [Set.finite_coe_iff] using Finite.finite_mulAction_orbit _
  exact Finite.instSigma

variable (β)

@[to_additive]
/-
**MulAction.orbitRel_le_fst** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：orbitRel_le_fst : orbitRel G (α × β) <= (orbitRel G α).comap Prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Setoid.le_def`：le_def {r s : Setoid α} : r <= s ↔ forall {x y}, r x y ->
 s x y
· 使用引理 `MulAction.fst_mem_orbit_of_mem_orbit`：fst_mem_orbit_of_mem_orbit {x y : 
α × β} (h : x in MulAction.orbit M y) : x.1 in MulAction.orbit M y.1
-/
lemma orbitRel_le_fst :
    orbitRel G (α × β) ≤ (orbitRel G α).comap Prod.fst :=
  Setoid.le_def.2 fst_mem_orbit_of_mem_orbit

@[to_additive]
/-
**MulAction.orbitRel_le_snd** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：orbitRel_le_snd : orbitRel G (α × β) <= (orbitRel G β).comap Prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Setoid.le_def`：le_def {r s : Setoid α} : r <= s ↔ forall {x y}, r x y ->
 s x y
· 使用引理 `MulAction.snd_mem_orbit_of_mem_orbit`：snd_mem_orbit_of_mem_orbit {x y : 
α × β} (h : x in MulAction.orbit M y) : x.2 in MulAction.orbit M y.2
-/
lemma orbitRel_le_snd :
    orbitRel G (α × β) ≤ (orbitRel G β).comap Prod.snd :=
  Setoid.le_def.2 snd_mem_orbit_of_mem_orbit

end Orbit

section Stabilizer

@[to_additive (attr := simp)]
/-
**MulAction._root_.IsCancelSMul.stabilizer_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Mul
Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsCancelSMul.stabilizer_eq_bot [IsCancelSMul G α] (a : α) :
    stabilizer G a = ⊥ :=
  Subgroup.eq_bot_iff_forall _ |>.mpr fun _ hg ↦ IsCancelSMul.eq_one_of_smul hg

@[to_additive]
/-
**MulAction._root_.isCancelSMul_iff_stabilizer_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 
`MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isCancelSMul_iff_stabilizer_eq_bot :
    IsCancelSMul G α ↔ (∀ a : α, stabilizer G a = ⊥) := by
  simp [isCancelSMul_iff_eq_one_of_smul_eq, Subgroup.eq_bot_iff_forall, forall_comm (α := G)]

/-- If the stabilizer of `a` is `S`, then the stabilizer of `g • a` is `gSg⁻¹`. -/
@[to_additive /-- If the stabilizer of `a` is `S`, then the stabilizer of `g +ᵥ a` is `g+S-g`. -/]
/-
**MulAction.stabilizer_smul_eq_stabilizer_map_conj** 是 Mathlib 中的一个定理，位于命名空间 `Mu
lAction`。
形式化陈述：stabilizer_smul_eq_stabilizer_map_conj (g : G) (a : α) : stabilizer G (g •
 a) = (stabilizer G a).map (MulAut.conj g).toMonoidHom
参数：g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_left_cancel_iff`：smul_left_cancel_iff (g : α) {x y : β} : g • x = g
 • y ↔ x = y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Subgroup.mem_map_equiv`：mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x :
 N} : x in K.map f.toMonoidHom ↔ f.symm x in K
· 使用定理 `MulAut.conj_symm_apply`：∀ {G : Type u_3} [inst : Group G] (g h : G), (Mu
lEquiv.symm (MulAut.conj g)) h = g⁻¹ * h * g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If the stabilizer of `a` is `S`, then the stabilizer of `g • a` is `gSg⁻¹`.
-/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : G) (a : α) :
    stabilizer G (g • a) = (stabilizer G a).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul,
    inv_mul_cancel, one_smul, ← mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

variable {g h k : G} {a b c : α}

/-- The natural group equivalence between the stabilizers of two elements in the same orbit. -/
@[to_additive /-- The isomorphism between the stabilizers of two elements in the same orbit. -/]
/-
**MulAction.stabilizerEquivStabilizer** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：stabilizerEquivStabilizer (hg : b = g • a) : stabilizer G a ≃* stabilizer 
G b
参数：hg : b = g • a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural group equivalence between the stabilizers of two elements in the sam
e orbit.
-/
def stabilizerEquivStabilizer (hg : b = g • a) : stabilizer G a ≃* stabilizer G b :=
  ((MulAut.conj g).subgroupMap (stabilizer G a)).trans
    (MulEquiv.subgroupCongr (by
      rw [hg, stabilizer_smul_eq_stabilizer_map_conj g a, ← MulEquiv.toMonoidHom_eq_coe]))

@[to_additive]
/-
**MulAction.stabilizerEquivStabilizer_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAction
`。
形式化陈述：stabilizerEquivStabilizer_apply (hg : b = g • a) (x : stabilizer G a) : st
abilizerEquivStabilizer hg x = MulAut.conj g x
参数：hg : b = g • a；x : stabilizer G a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stabilizerEquivStabilizer_apply (hg : b = g • a) (x : stabilizer G a) :
    stabilizerEquivStabilizer hg x = MulAut.conj g x := by
  simp [stabilizerEquivStabilizer]

@[to_additive]
/-
**MulAction.stabilizerEquivStabilizer_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulA
ction`。
形式化陈述：stabilizerEquivStabilizer_symm_apply (hg : b = g • a) (x : stabilizer G b)
 : (stabilizerEquivStabilizer hg).symm x = MulAut.conj g⁻¹ x
参数：hg : b = g • a；x : stabilizer G b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulAut.inv_apply`：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M)
, e⁻¹ m = (MulEquiv.symm e) m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stabilizerEquivStabilizer_symm_apply (hg : b = g • a) (x : stabilizer G b) :
    (stabilizerEquivStabilizer hg).symm x = MulAut.conj g⁻¹ x := by
  simp [stabilizerEquivStabilizer]

@[to_additive]
/-
**MulAction.stabilizerEquivStabilizer_trans** 是 Mathlib 中的一个定理，位于命名空间 `MulAction
`。
形式化陈述：stabilizerEquivStabilizer_trans (hg : b = g • a) (hh : c = h • b) (hk : c 
= k • a) (H : k = h * g) : (stabilizerEquivStabilizer hg).trans (stabilizerEquiv
Stabilizer hh) = stabilizerEquivStabilizer hk
参数：hg : b = g • a；hh : c = h • b；hk : c = k • a；H : k = h * g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.stabilizerEquivStabilizer_apply`：stabilizerEquivStabilizer_app
ly (hg : b = g • a) (x : stabilizer G a) : stabilizerEquivStabilizer hg x = MulA
ut.conj g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulAction.stabilizerEquivStabilizer.congr_simp`：∀ {G : Type u_1} {α : Ty
pe u_2} [inst : Group G] [inst_1 : MulAction G α] {g g_1 : G} (e_g : g = g_1) {a
 b : α}   (hg : b = g • a), MulActio…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stabilizerEquivStabilizer_trans (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)
    (H : k = h * g) :
    (stabilizerEquivStabilizer hg).trans (stabilizerEquivStabilizer hh) =
      stabilizerEquivStabilizer hk := by
  ext; simp [stabilizerEquivStabilizer_apply, H]

@[to_additive]
/-
**MulAction.stabilizerEquivStabilizer_one** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：stabilizerEquivStabilizer_one : stabilizerEquivStabilizer (one_smul G a).s
ymm = MulEquiv.refl (stabilizer G a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.stabilizerEquivStabilizer_apply`：stabilizerEquivStabilizer_app
ly (hg : b = g • a) (x : stabilizer G a) : stabilizerEquivStabilizer hg x = MulA
ut.conj g x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stabilizerEquivStabilizer_one :
    stabilizerEquivStabilizer (one_smul G a).symm = MulEquiv.refl (stabilizer G a) := by
  ext; simp [stabilizerEquivStabilizer_apply]

@[to_additive]
/-
**MulAction.stabilizerEquivStabilizer_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：stabilizerEquivStabilizer_symm (hg : b = g • a) : (stabilizerEquivStabiliz
er hg).symm = stabilizerEquivStabilizer (eq_inv_smul_iff.mpr hg.symm)
参数：hg : b = g • a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulAut.inv_apply`：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M)
, e⁻¹ m = (MulEquiv.symm e) m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stabilizerEquivStabilizer_symm (hg : b = g • a) :
    (stabilizerEquivStabilizer hg).symm =
      stabilizerEquivStabilizer (eq_inv_smul_iff.mpr hg.symm) := by
  ext x; simp [stabilizerEquivStabilizer]

@[to_additive]
/-
**MulAction.stabilizerEquivStabilizer_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：stabilizerEquivStabilizer_inv (hg : b = g⁻¹ • a) : stabilizerEquivStabiliz
er hg = (stabilizerEquivStabilizer (inv_smul_eq_iff.mp hg.symm)).symm
参数：hg : b = g⁻¹ • a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulAut.inv_apply`：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M)
, e⁻¹ m = (MulEquiv.symm e) m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stabilizerEquivStabilizer_inv (hg : b = g⁻¹ • a) :
    stabilizerEquivStabilizer hg =
      (stabilizerEquivStabilizer (inv_smul_eq_iff.mp hg.symm)).symm := by
  ext; simp [stabilizerEquivStabilizer]

/-- A isomorphism between the stabilizers of two elements in the same orbit. -/
@[to_additive /-- A isomorphism between the stabilizers of two elements in the same orbit. -/]
/-
**MulAction.stabilizerEquivStabilizerOfOrbitRel** 是 Mathlib 中的一个定义，位于命名空间 `MulAc
tion`。
形式化陈述：stabilizerEquivStabilizerOfOrbitRel (h : orbitRel G α a b) : stabilizer G 
a ≃* stabilizer G b
参数：h : orbitRel G α a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A isomorphism between the stabilizers of two elements in the same orbit.
-/
noncomputable def stabilizerEquivStabilizerOfOrbitRel (h : orbitRel G α a b) :
    stabilizer G a ≃* stabilizer G b :=
  (stabilizerEquivStabilizer (Classical.choose_spec h).symm).symm

end Stabilizer

end MulAction

namespace AddAction

@[deprecated (since := "2026-05-26")] alias stabilizer_vadd_eq_stabilizer_map_conj :=
  stabilizer_vadd_eq_stabilizer_map_addConj

end AddAction

/-
**Equiv.swap_mem_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.swap_mem_stabilizer {α : Type*} [DecidableEq α] {S : Set α} {a b : α
} : Equiv.swap a b in MulAction.stabilizer (Equiv.Perm α) S ↔ (a in S ↔ b in S)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.swap_inv`：∀ {α : Type u_4} [inst : DecidableEq α] (x y : α), (Equi
v.swap x y)⁻¹ = Equiv.swap x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem Equiv.swap_mem_stabilizer {α : Type*} [DecidableEq α] {S : Set α} {a b : α} :
    Equiv.swap a b ∈ MulAction.stabilizer (Equiv.Perm α) S ↔ (a ∈ S ↔ b ∈ S) := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff, ← swap_inv]
  simp_rw [Set.mem_inv_smul_set_iff, Perm.smul_def, swap_apply_def]
  exact ⟨fun h ↦ by simpa [Iff.comm] using h a, by intros; split_ifs <;> simp [*]⟩

namespace MulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions. -/
@[to_additive
  /-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions. -/]
/-
**MulAction.le_stabilizer_iff_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：le_stabilizer_iff_smul_le (s : Set α) (H : Subgroup G) : H <= stabilizer G
 s ↔ forall g in H, g • s subseteq s
参数：s : Set α；H : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_stabilizer_iff_smul_le (s : Set α) (H : Subgroup G) :
    H ≤ stabilizer G s ↔ ∀ g ∈ H, g • s ⊆ s := by
  constructor
  · intro hyp g hg
    apply Eq.subset
    rw [← mem_stabilizer_iff]
    exact hyp hg
  · intro hyp g hg
    rw [mem_stabilizer_iff]
    apply subset_antisymm (hyp g hg)
    intro x hx
    use g⁻¹ • x
    constructor
    · apply hyp g⁻¹ (inv_mem hg)
      simp only [Set.smul_mem_smul_set_iff, hx]
    · simp only [smul_inv_smul]

end MulAction

section
variable (R M : Type*) [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [IsTorsionFree R M]

variable {M} in
/-
**Module.stabilizer_units_eq_bot_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.stabilizer_units_eq_bot_of_ne_zero {x : M} (hx : x != 0) : MulActio
n.stabilizer Rˣ x = ⊥
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `smul_eq_zero_iff_left`：smul_eq_zero_iff_left (hm : m != 0) : r • m = 0 ↔
 r = 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma Module.stabilizer_units_eq_bot_of_ne_zero {x : M} (hx : x ≠ 0) :
    MulAction.stabilizer Rˣ x = ⊥ := by
  rw [eq_bot_iff]
  intro g (hg : g.val • x = x)
  ext
  rw [← sub_eq_zero, ← smul_eq_zero_iff_left hx, Units.val_one, sub_smul, hg, one_smul, sub_self]

end

/-
**Multiplicative.mulAction_orbit** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : VAdd α β] (b : β), MulAction.orbit
 (Multiplicative α) b = AddAction.orbit α b
参数：b : β；Multiplicative α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Multiplicative.mulAction_orbit {α β : Type*} [VAdd α β] (b : β) :
    MulAction.orbit (Multiplicative α) b = AddAction.orbit α b :=
  rfl
/-
**Additive.mulAction_orbit** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : SMul α β] (b : β), AddAction.orbit
 (Additive α) b = MulAction.orbit α b
参数：b : β；Additive α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Additive.mulAction_orbit {α β : Type*} [SMul α β] (b : β) :
    AddAction.orbit (Additive α) b = MulAction.orbit α b :=
  rfl
